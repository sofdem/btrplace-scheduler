package btrplace.solver.api.cstrSpec.reducer;

import btrplace.model.Model;
import btrplace.model.Node;
import btrplace.model.VM;
import btrplace.model.constraint.SatConstraint;
import btrplace.plan.DefaultReconfigurationPlan;
import btrplace.plan.ReconfigurationPlan;
import btrplace.plan.event.Action;
import btrplace.plan.event.VMEvent;
import btrplace.solver.api.cstrSpec.Constraint;
import btrplace.solver.api.cstrSpec.spec.term.Constant;
import btrplace.solver.api.cstrSpec.verification.TestCase;
import btrplace.solver.api.cstrSpec.verification.Verifier;

import java.util.ArrayList;
import java.util.List;
import java.util.ListIterator;

/**
 * Remove supposed useless VMs or nodes.
 * <p/>
 * This try to remove one by one VMs or nodes that are not involved
 * in the constraint. The actions that manipulate these elements are removed too.
 * An element is maintained in the plan if its removal changes the error
 *
 * @author Fabien Hermenier
 */
public class ElementsReducer {

    private Verifier v;

    public ElementsReducer(Verifier v) {
        this.v = v;
    }

    private boolean consistent(ReconfigurationPlan p, Constraint cstr, List<Constant> in) throws Exception {
        TestCase tc = new TestCase(v, cstr, p, in, true);
        return tc.succeed();
    }

    public ReconfigurationPlan reduce(ReconfigurationPlan p, Constraint cstr, List<Constant> in) throws Exception {
        ReconfigurationPlan r1 = reduceVMs(p, cstr, in);
        return reduceNodes(r1, cstr, in);
    }

    public ReconfigurationPlan reduceVMs(ReconfigurationPlan p, Constraint cstr, List<Constant> in) throws Exception {
        if (consistent(p, cstr, in)) {
            return p;
        }
        SatConstraint s = cstr.instantiate(in);
        List<VM> l = new ArrayList<>(p.getOrigin().getMapping().getAllVMs());
        l.removeAll(s.getInvolvedVMs());
        ListIterator<VM> ite = l.listIterator();

        Model mo = p.getOrigin().clone();
        ReconfigurationPlan red = p;
        while (ite.hasNext()) {
            red = new DefaultReconfigurationPlan(mo);
            VM v = ite.next();
            ite.remove();
            int state;
            Node h = null;
            if (mo.getMapping().isReady(v)) {
                state = 0;
            } else if (mo.getMapping().isRunning(v)) {
                state = 1;
            } else {
                state = 2;
            }
            if (state != 0) {
                h = mo.getMapping().getVMLocation(v);
            }

            mo.getMapping().remove(v);
            for (Action a : p) {
                if (a instanceof VMEvent) {
                    if (mo.getMapping().contains(((VMEvent) a).getVM())) {
                        red.add(a);
                    }
                } else {
                    red.add(a);
                }
            }
            if (consistent(red, cstr, in)) {
                //The VM must be present, put it back
                if (state == 0) {
                    mo.getMapping().addReadyVM(v);
                } else if (state == 1) {
                    mo.getMapping().addRunningVM(v, h);
                } else {
                    mo.getMapping().addSleepingVM(v, h);
                }
                ite.add(v);
            }
        }
        return red;
    }

    public ReconfigurationPlan reduceNodes(ReconfigurationPlan p, Constraint cstr, List<Constant> in) throws Exception {
        if (consistent(p, cstr, in)) {
            return p;
        }
        SatConstraint s = cstr.instantiate(in);
        List<Node> l = new ArrayList<>(p.getOrigin().getMapping().getAllNodes());
        l.removeAll(s.getInvolvedNodes());
        ListIterator<Node> ite = l.listIterator();

        Model mo = p.getOrigin().clone();
        ReconfigurationPlan red = p;
        while (ite.hasNext()) {
            red = new DefaultReconfigurationPlan(mo);
            Node n = ite.next();
            ite.remove();
            boolean on = mo.getMapping().isOnline(n);
            if (mo.getMapping().remove(n)) {
                for (Action a : p) {
                    red.add(a);
                }
                if (red.isApplyable()) {
                    //TestResult.ErrorType e = consistent(red, cstr, in);
                    if (consistent(red, cstr, in)) {
                        //The node must be present, put it back
                        if (on) {
                            mo.getMapping().addOnlineNode(n);
                        } else {
                            mo.getMapping().addOfflineNode(n);
                        }
                        ite.add(n);
                    }
                } else {
                    //The node must be present, put it back
                    if (on) {
                        mo.getMapping().addOnlineNode(n);
                    } else {
                        mo.getMapping().addOfflineNode(n);
                    }
                    ite.add(n);
                }
            }
        }
        return red;
    }
}