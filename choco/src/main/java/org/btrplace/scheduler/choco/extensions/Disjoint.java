/*
 * Copyright  2022 The BtrPlace Authors. All rights reserved.
 * Use of this source code is governed by a LGPL-style
 * license that can be found in the LICENSE.txt file.
 */

package org.btrplace.scheduler.choco.extensions;


import org.chocosolver.memory.IStateInt;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.delta.IIntDeltaMonitor;
import org.chocosolver.solver.variables.events.IntEventType;
import org.chocosolver.util.ESat;
import org.chocosolver.util.procedure.UnaryIntProcedure;
import org.chocosolver.util.tools.ArrayUtils;

/**
 * Enforces fixed sets of variables to have disjoint sets of values.
 * Incremental filtering and supporting structures are designed for instances with few sets and values but many vars.
 * created sofdem - 08/09/11
 *
 * @author Sophie Demassey
 */
public class Disjoint extends Constraint {

    /**
     * @param vs sets of variables vs[nbSets][nbVarsInSet]
     * @param c  max variable value + 1
     */
    public Disjoint(IntVar[][] vs, int c) {
        super("Disjoint", new DisjointPropagator(vs, c));
    }

    static class DisjointPropagator extends Propagator<IntVar> {

        /**
         * the variable domains are included in [0, nbValues-1]
         */
        private final int nbValues;

        /**
         * the number of sets
         */
        private final int nbSets;

        /**
         * indices of the variables in 'vars' belonging to set 's' are between 'setIdx[s]' and 'setIdx[s+1]'
         * with 0 <= s < nbSets
         */
        private final int[] setIdx;

        /**
         * candidates[s][v] = maximum number of variables in set 's' which can be assigned to value 'v',
         * with 0 <= s < nbSets and 0 <= v < nbValues
         */
        private final IStateInt[][] candidates;

        /**
         * reserved[v] = s+1 iff at least one variable in set 's' is assigned to value 'v' (care of the offset +1)
         * with 0 <= s < nbSets and 0 <= v < nbValues
         */
        private final IStateInt[] reserved;

        private final IIntDeltaMonitor[] idms;

        private boolean first = true;

        private final RemProc remProc;

        /**
         * @param vs sets of variables
         * @param c  max variable value + 1
         */
        public DisjointPropagator(IntVar[][] vs, int c) {
            super(ArrayUtils.flatten(vs), PropagatorPriority.VERY_SLOW, true);
            nbValues = c;
            nbSets = vs.length;
            setIdx = new int[nbSets + 1];
            candidates = new IStateInt[nbSets][c];
            reserved = new IStateInt[nbValues];

            setIdx[0] = 0;
            int idx = 0;
            for (int s = 0; s < nbSets; s++) {
                idx += vs[s].length;
                setIdx[s + 1] = idx;
                for (int v = 0; v < nbValues; v++) {
                    candidates[s][v] = getModel().getEnvironment().makeInt(0);
                }
            }
            for (int v = 0; v < nbValues; v++) {
                reserved[v] = getModel().getEnvironment().makeInt(0);
            }

            idms = new IIntDeltaMonitor[vars.length];
            int i = 0;
            for (IntVar v : vars) {
                idms[i++] = v.monitorDelta(this);
            }
            remProc = new RemProc();
        }

        @Override
        public int getPropagationConditions(int vIdx) {
            //TODO: REMOVE should be fine
            return IntEventType.all();
        }

        /**
          Check for every value 'v' that the variables assigned to 'v' all belong to the same set
         */
        @Override
        public ESat isEntailed() {
            // usedBy[v]=s+1 if value 'v' is assigned to vars in set 's', usedBy[v]= if 'v' is not assigned
            final int[] usedBy = new int[nbValues];
            int i = 0;
            for (int s = 1; s <= nbSets; s++) {
                for (; i < setIdx[s]; i++) {
                    int v = vars[i].getValue();
                    if (usedBy[v] == 0) {
                        usedBy[v] = s;
                    } else if (usedBy[v] < s) {
                        return ESat.FALSE;
                    }
                }
            }
            return ESat.TRUE;
        }

        /**
         * At initial propagation: fill in 'resTmp' or 'candidate'  if 'var' is instantiated or not
         *
         * @param var    the variable index
         * @param varSet the variable set index
         * @param resTmp a temporary copy for reserved for the initial propagation
         * @throws ContradictionException if 'var' is instantiated to a value reserved to another set than 'varSet'
         */
        private int initVar(IntVar var, int varSet, int[] resTmp) throws ContradictionException {
            int val = -1;
            if (var.isInstantiated()) {
                val = var.getValue();
                if (resTmp[val] == 0) {
                    resTmp[val] = varSet + 1;
                } else if (resTmp[val] != varSet + 1) {
                    fails();
                }
            }
            int ub = var.getUB();
            assert ub < nbValues;
            for (int v = var.getLB(); v <= ub; v = var.nextValue(v)) {
                candidates[varSet][v].add(1);
            }
            return val;
        }

        /**
         * First propagation: initialize 'reserved' and 'candidates' then propagate the instantiations
         */
        @Override
        public void propagate(int m) throws ContradictionException {
            assert first;
            // a temporary copy for 'reserved' before the first propagation (using same offset +1)
            int[] resTmp = new int[nbValues];
            // save the first and last instantiated values to prevent to loop over all values
            int firstVal = nbValues;
            int lastVal = -1;
            int i = 0;
            for (int s = 0; s < nbSets; s++) {
                for (; i < setIdx[s + 1]; i++) {
                    int resVal = initVar(vars[i], s, resTmp);
                    if (resVal >= 0) {
                        if (resVal < firstVal) {
                            firstVal = resVal;
                        }
                        if (lastVal < resVal) {
                            lastVal = resVal;
                        }
                    }
                }
            }

            for (final IIntDeltaMonitor dm : idms) {
                dm.startMonitoring();
            }
            // propagate the instantiations discovered in 'resTmp' and initialize 'reserved'
            for (int v = firstVal; v <= lastVal; v++) {
                if (resTmp[v] > 0) {
                    reserveValue(resTmp[v] - 1, v);
                }
            }
            first = false;
        }

        @Override
        public void propagate(int idx, int mask) throws ContradictionException {
            if (IntEventType.isInstantiate(mask)) {
                reserveValue(getVarSet(idx), vars[idx].getValue());
            }
            if (IntEventType.isRemove(mask)) {
                idms[idx].forEachRemVal(remProc.set(getVarSet(idx)));
            }
        }

        /**
         * propagate the assignment of value 'val' to variable set 'varSet' recursively:
         * 0) do nothing if already assigned
         * 1) fail if 'val' is already assigned to another set
         * 2) remove 'val' from the variables in the other candidate sets and propagate the possible new instantiations
         *
         * @param varSet the variable set
         * @param val    the value
         * @throws ContradictionException if some variables in different sets are instantiated to the same value
         */
        public void reserveValue(int varSet, int val) throws ContradictionException {
            int resSet = reserved[val].get();

            // 0/ do nothing if 'val' is already assigned to 'varSet'
            if (resSet == varSet + 1) {
                return;
            }
            // 1/ throw contradiction if 'val' is already assigned to another set than 'varSet'
            if (resSet > 0) {
                fails();
            }
            reserved[val].set(varSet + 1);
            // 2/ remove 'val' from the variables in the other sets, trying not to visit all the variables by using
            // 'candidates[s][val]' which estimates the maximum number of vars to consider in set s
            // may temporarily be > to the actual number because of the recursion (not a bug, just extra work).
            int i = 0;
            for (int s = 0; s < nbSets; s++) {
                int c = (s==varSet) ? 0: candidates[s][val].get();
                i = setIdx[s];
                for (; c > 0 && i < setIdx[s + 1]; i++) {
                    if (vars[i].removeValue(val, this)) {
                        c--;
                        if (vars[i].isInstantiated()) {
                            reserveValue(s, vars[i].getValue());
                        }
                    }
                }
                candidates[s][val].set(0);
            }
        }

        /**
         * Get the set of a given variable.
         * This lookup is done recursively by dichotomy.
         *
         * @param varIdx the variable.
         * @return the set.
         */
        private int getVarSet(int varIdx) {
            return getVarSet(varIdx, 0, nbSets);
        }

        private int getVarSet(int varIdx, int s, int e) {
            assert e > s && setIdx[s] <= varIdx && varIdx < setIdx[e];
            if (e == s + 1) {
                return s;
            }
            // Complicated average computation that should prevent an overflow
            //from findbug point of view.
            int m = (s + e) >>> 1;
            if (varIdx >= setIdx[m]) {
                return getVarSet(varIdx, m, e);
            }
            return getVarSet(varIdx, s, m);

        }

        private class RemProc implements UnaryIntProcedure<Integer> {
            private int set;

            @Override
            public UnaryIntProcedure<Integer> set(Integer set) {
                this.set = set;
                return this;
            }

            @Override
            public void execute(int val) {
                candidates[set][val].add(-1);
            }
        }


        private void checkCandidates(int s, int val) {
            if (reserved[val].get() == s + 1) {
                return;
            }
            int c = candidates[s][val].get();
            int nbVars = 0;
            for (int i = setIdx[s]; i < setIdx[s + 1]; i++) {
                if (vars[i].contains(val)) {
                    nbVars++;
                }
            }
            assert c >= nbVars : "candidates[" + s + "," + val + "] de-synchronized:" + c + " expected, " + nbVars + " found";
        }


        private void checkCandidates(boolean check) {
            for (int s = 0; s < nbSets; s++) {
                for (int v = 0; v < nbValues; v++) {
                    int c = candidates[s][v].get();
                    if (c != 0) {
                        if (check) {
                            checkCandidates(s, v);
                        }
                        System.out.println("candidates[" + s + "," + v + "] = " + c);
                    }
                }
            }
        }
    }
}
