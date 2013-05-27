/*
 * Copyright (c) 2013 University of Nice Sophia-Antipolis
 *
 * This file is part of btrplace.
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package btrplace.solver.choco.actionModel;

import btrplace.plan.ReconfigurationPlan;
import btrplace.plan.event.BootVM;
import btrplace.solver.SolverException;
import btrplace.solver.choco.ReconfigurationProblem;
import btrplace.solver.choco.Slice;
import btrplace.solver.choco.SliceBuilder;
import choco.cp.solver.CPSolver;
import choco.cp.solver.variables.integer.IntDomainVarAddCste;
import choco.kernel.solver.variables.integer.IntDomainVar;


/**
 * Model an action that boot a VM in the ready state.
 * The model must provide an estimation of the action duration through a
 * {@link btrplace.solver.choco.durationEvaluator.DurationEvaluator} accessible from
 * {@link btrplace.solver.choco.ReconfigurationProblem#getDurationEvaluators()} with the key {@code BootVM.class}
 * <p/>
 * If the reconfiguration problem has a solution, a {@link btrplace.plan.event.BootVM} action
 * is inserted into the resulting reconfiguration plan.
 *
 * @author Fabien Hermenier
 */
public class BootVMModel implements VMActionModel {

    private Slice dSlice;

    private IntDomainVar end;

    private IntDomainVar start;

    private IntDomainVar duration;

    private int vm;

    private ReconfigurationProblem rp;

    private IntDomainVar state;

    /**
     * Make a new model.
     *
     * @param rp the RP to use as a basis.
     * @param e  the VM managed by the action
     * @throws SolverException if an error occurred
     */
    public BootVMModel(ReconfigurationProblem rp, int e) throws SolverException {
        vm = e;

        int d = rp.getDurationEvaluators().evaluate(rp.getSourceModel(), BootVM.class, e);
        this.rp = rp;
        start = rp.makeDuration(rp.getEnd().getSup() - d, 0, "bootVM(", e, ").start");
        end = new IntDomainVarAddCste(rp.getSolver(), rp.makeVarLabel("bootVM(", e, ").end"), start, d);
        duration = rp.makeDuration(d, d, "bootVM.duration(", e, ')');
        dSlice = new SliceBuilder(rp, e, new StringBuilder("bootVM(").append(e).append(").dSlice").toString()).setStart(start)
                .setDuration(rp.makeDuration(rp.getEnd().getSup(), d, "bootVM(", e, ").dSlice_duration"))
                .build();
        CPSolver s = rp.getSolver();
        s.post(s.leq(start, rp.getEnd()));
        s.post(s.leq(duration, rp.getEnd()));
        s.post(s.leq(end, rp.getEnd()));

        state = s.makeConstantIntVar(1);
    }

    @Override
    public boolean insertActions(ReconfigurationPlan plan) {
        int node = rp.getNode(dSlice.getHoster().getVal());
        BootVM a = new BootVM(vm, node, start.getVal(), end.getVal());
        plan.add(a);
        return true;
    }

    @Override
    public IntDomainVar getStart() {
        return start;
    }

    @Override
    public IntDomainVar getEnd() {
        return end;
    }

    @Override
    public IntDomainVar getDuration() {
        return duration;
    }

    @Override
    public Slice getCSlice() {
        return null;
    }

    @Override
    public Slice getDSlice() {
        return dSlice;
    }

    @Override
    public IntDomainVar getState() {
        return state;
    }

    @Override
    public int getVM() {
        return vm;
    }

    @Override
    public void visit(ActionModelVisitor v) {
        v.visit(this);
    }


}
