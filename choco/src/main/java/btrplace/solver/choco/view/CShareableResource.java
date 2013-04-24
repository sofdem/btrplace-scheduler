/*
 * Copyright (c) 2012 University of Nice Sophia-Antipolis
 *
 * This file is part of btrplace.
 *
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

package btrplace.solver.choco.view;

import btrplace.model.Mapping;
import btrplace.model.Model;
import btrplace.model.ModelView;
import btrplace.model.view.ShareableResource;
import btrplace.plan.Action;
import btrplace.plan.ReconfigurationPlan;
import btrplace.plan.RunningVMPlacement;
import btrplace.plan.event.Allocate;
import btrplace.plan.event.AllocateEvent;
import btrplace.solver.SolverException;
import btrplace.solver.choco.*;
import btrplace.solver.choco.actionModel.KeepRunningVMModel;
import btrplace.solver.choco.chocoUtil.ChocoUtils;
import btrplace.solver.choco.chocoUtil.FastImpliesEq;
import choco.Choco;
import choco.cp.solver.CPSolver;
import choco.kernel.solver.ContradictionException;
import choco.kernel.solver.variables.integer.IntDomainVar;
import choco.kernel.solver.variables.real.RealIntervalConstant;
import choco.kernel.solver.variables.real.RealVar;
import gnu.trove.TIntArrayList;

import java.util.ArrayList;
import java.util.List;
import java.util.UUID;

/**
 * Specify, for a given resource, the physical resource usage associated to each server,
 * and the virtual resource usage consumed by each of the VMs they host.
 *
 * @author Fabien Hermenier
 */
public class CShareableResource implements ChocoModelView {

    private ShareableResource rc;

    private IntDomainVar[] phyRcUsage;

    private IntDomainVar[] virtRcUsage;

    private IntDomainVar[] vmAllocation;

    private RealVar[] ratios;

    private ReconfigurationProblem rp;

    private CPSolver solver;

    private String id;

    private Model source;

    /**
     * The default value of ratio is not logical to detect an unchanged value
     */
    public static final double UNCHECKED_RATIO = Double.MAX_VALUE / 100;

    /**
     * Make a new mapping.
     *
     * @param rp the problem to rely on
     * @param rc the resource to consider
     */
    public CShareableResource(ReconfigurationProblem rp, ShareableResource rc) {
        this.rc = rc;
        this.rp = rp;
        solver = rp.getSolver();
        this.source = rp.getSourceModel();
        UUID[] nodes = rp.getNodes();
        phyRcUsage = new IntDomainVar[nodes.length];
        virtRcUsage = new IntDomainVar[nodes.length];
        this.ratios = new RealVar[nodes.length];
        id = ShareableResource.VIEW_ID_BASE + rc.getResourceIdentifier();
        for (int i = 0; i < nodes.length; i++) {
            UUID nId = rp.getNode(i);
            phyRcUsage[i] = rp.getSolver().createBoundIntVar(rp.makeVarLabel("phyRcUsage('", rc.getResourceIdentifier(), "', '", nId, "')"), 0, rc.get(nodes[i]));
            virtRcUsage[i] = rp.getSolver().createBoundIntVar(rp.makeVarLabel("virtRcUsage('", rc.getResourceIdentifier(), "', '", nId, "')"), 0, Choco.MAX_UPPER_BOUND);
            ratios[i] = rp.getSolver().createRealVal(rp.makeVarLabel("overbook('", rc.getResourceIdentifier(), "', '", nId, "')"), 1, UNCHECKED_RATIO);
        }


        //Bin packing for the node vmAllocation
        CPSolver s = rp.getSolver();
        List<IntDomainVar> notNullUsage = new ArrayList<>();
        List<IntDomainVar> hosters = new ArrayList<>();

        vmAllocation = new IntDomainVar[rp.getVMs().length];
        for (int i = 0; i < vmAllocation.length; i++) {
            UUID vmId = rp.getVM(i);
            VMActionModel a = rp.getVMAction(vmId);
            Slice slice = a.getDSlice();
            if (slice == null) { //The VMs will not be running, so its consumption is set to 0
                vmAllocation[i] = s.makeConstantIntVar(rp.makeVarLabel("vmAllocation('", rc.getResourceIdentifier(), "', '", vmId, "'"), 0);
            } else {
                //We don't know about the next VM usage for the moment, -1 is used by default to allow to detect an
                //non-updated value.
                vmAllocation[i] = s.createBoundIntVar(rp.makeVarLabel("vmAllocation('", rc.getResourceIdentifier(), "', '", vmId, "')"), -1, Choco.MAX_UPPER_BOUND);
                notNullUsage.add(vmAllocation[i]);
                hosters.add(slice.getHoster());
            }

        }
        //We create a BP with only the VMs requiring a not null amount of resources
        //s.post(new LightBinPacking(s.getEnvironment(), virtRcUsage, notNullUsage.toArray(new IntDomainVar[notNullUsage.size()]), hosters.toArray(new IntDomainVar[hosters.size()])));
        //s.post(new BinPacking(s.getEnvironment(), virtRcUsage, notNullUsage.toArray(new IntDomainVar[notNullUsage.size()]), hosters.toArray(new IntDomainVar[hosters.size()])));
        rp.getBinPackingBuilder().add(getResourceIdentifier(), virtRcUsage, notNullUsage.toArray(new IntDomainVar[notNullUsage.size()]), hosters.toArray(new IntDomainVar[hosters.size()]));

    }

    /**
     * Get the resource identifier.
     *
     * @return an identifier
     */
    public String getResourceIdentifier() {
        return rc.getResourceIdentifier();
    }

    /**
     * Get the original resource node physical capacity and VM consumption.
     *
     * @return an {@link ShareableResource}
     */
    public ShareableResource getSourceResource() {
        return rc;
    }

    /**
     * Get the physical resource usage of each node.
     *
     * @return an array of variable denoting the resource usage for each node.
     */
    public IntDomainVar[] getPhysicalUsage() {
        return phyRcUsage;
    }

    /**
     * Get the physical resource usage of a given node
     *
     * @param nIdx the node identifier
     * @return the variable denoting the resource usage for the node. {@code null} if the node is unknown
     */
    public IntDomainVar getPhysicalUsage(int nIdx) {
        if (nIdx >= 0 && nIdx < rp.getNodes().length) {
            return phyRcUsage[nIdx];
        }
        return null;
    }

    /**
     * Get the virtual resource usage  that is made by the VMs on the nodes.
     * <b>Warning: the only possible approach to restrict these value is to increase their
     * upper bound using the associated {@code setSup()} method</b>
     *
     * @return an array of variables denoting each node virtual resource usage.
     */
    public IntDomainVar[] getVirtualUsage() {
        return virtRcUsage;
    }

    /**
     * Get the virtual resource usage of a given node.
     * <b>Warning: the only possible approach to restrict the value is to increase their
     * upper bound using the associated {@code setSup()} method</b>
     *
     * @param nIdx the node identifier
     * @return the variable denoting the resource usage for the node. {@code null} if the node is unknown
     */
    public IntDomainVar getVirtualUsage(int nIdx) {
        if (nIdx >= 0 && nIdx < rp.getNodes().length) {
            return virtRcUsage[nIdx];
        }
        return null;
    }

    /**
     * Get the amount of virtual resource to allocate to each VM.
     * <b>Warning: the only possible approach to restrict these value is to increase their
     * lower bound using the associated {@code setInf()} method</b>
     *
     * @return an array of variables denoting each VM vmAllocation
     */
    public IntDomainVar[] getVMsAllocation() {
        return vmAllocation;
    }

    /**
     * Get the amount of virtual resource to allocate a given VM.
     * <b>Warning: the only possible approach to restrict this value is to increase their
     * lower bound using the associated {@code setInf()} method</b>
     *
     * @param vmIdx the VM identifier
     * @return the variable denoting the virtual resources to allocate to the VM. {@code null} if the VM is unknown
     */
    public IntDomainVar getVMsAllocation(int vmIdx) {
        if (vmIdx >= 0 && vmIdx < rp.getVMs().length) {
            return vmAllocation[vmIdx];
        }
        return null;
    }

    /**
     * Get the overbooking ratio for a node.
     * <b>WARNING: it is only allowed to reduce the upper-bound of the ratio using {@code #setSup(x)} methods</b>
     *
     * @param nId the node identifier
     * @return an array of ratios.
     */
    public RealVar getOverbookRatio(int nId) {
        return ratios[nId];
    }

    /**
     * Get the overbooking ratios for every nodes.
     * <b>WARNING: it is only allowed to reduce the upper-bound of the ratio using {@code #setSup(x)} methods</b>
     *
     * @return an array of ratios.
     */
    public RealVar[] getOverbookRatios() {
        return ratios;
    }

    /**
     * Generate and add an {@link btrplace.plan.event.Allocate} action if the amount of
     * resources allocated to a VM has changed.
     * The action schedule must be known.
     *
     * @param e    the VM identifier
     * @param node the identifier of the node that is currently hosting the VM
     * @param st   the moment that action starts
     * @param ed   the moment the action ends
     * @return {@code true} if the action has been added to the plan,{@code false} otherwise
     */
    public boolean addAllocateAction(ReconfigurationPlan plan, UUID e, UUID node, int st, int ed) {

        int use = vmAllocation[rp.getVM(e)].getInf();
        if (rc.get(e) != use) {
            //The allocation has changed
            Allocate a = new Allocate(e, node, rc.getIdentifier(), use, st, ed);
            return plan.add(a);
        }
        return false;
    }

    @Override
    public String getIdentifier() {
        return id;
    }

    @Override
    public String toString() {
        return id;
    }

    /**
     * Builder associated to the constraint.
     */
    public static class Builder implements ChocoModelViewBuilder {
        @Override
        public Class<? extends ModelView> getKey() {
            return ShareableResource.class;
        }

        @Override
        public ChocoModelView build(ReconfigurationProblem rp, ModelView v) throws SolverException {
            ShareableResource rc = (ShareableResource) v;
            return new CShareableResource(rp, rc);
        }
    }

    /**
     * Set the resource usage for each of the VM.
     * If the LB is < 0 , the previous consumption is used to maintain the resource usage.
     * Otherwise, the usage is set to the variable lower bound.
     *
     * @return false if an operation leads to a problem without solution
     */
    @Override
    public boolean beforeSolve(ReconfigurationProblem rp) {
        for (UUID vm : source.getMapping().getAllVMs()) {
            int vmId = rp.getVM(vm);
            IntDomainVar v = vmAllocation[vmId];
            if (v.getInf() < 0) {
                int prevUsage = rc.get(vm);
                try {
                    v.setInf(prevUsage);
                } catch (ContradictionException e) {
                    rp.getLogger().error("Unable to set the minimal '{}' usage for '{}' to its current usage ({})",
                            rc.getResourceIdentifier(), vm, prevUsage);
                    return false;
                }
            } else {
                try {
                    v.setVal(v.getInf());
                } catch (ContradictionException e) {
                    rp.getLogger().error("Unable to set the VM '{}' consumption to '{}'", rc.getResourceIdentifier(), v.getInf());
                    return false;
                }
            }
        }

        return symmetryBreakingForStatingVMs() && linkVirtualToPhysicalUsage();
    }

    @Override
    public boolean insertActions(ReconfigurationProblem rp, ReconfigurationPlan p) {
        Mapping srcMapping = rp.getSourceModel().getMapping();

        for (UUID vm : rp.getFutureRunningVMs()) {
            Slice dSlice = rp.getVMAction(vm).getDSlice();
            UUID destNode = rp.getNode(dSlice.getHoster().getVal());

            if (srcMapping.getRunningVMs().contains(vm) && destNode.equals(srcMapping.getVMLocation(vm))) {
                //Was running and stay on the same node
                insertAllocateAction(p, vm, destNode, dSlice.getStart().getVal());
            } else {
                //TODO: not constant time operation. Maybe a big failure
                for (Action a : p) {
                    if (a instanceof RunningVMPlacement) {
                        RunningVMPlacement tmp = (RunningVMPlacement) a;
                        if (tmp.getVM().equals(vm)) {
                            insertAllocateEvent(a, vm);
                            break;
                        }
                    }
                }
            }
        }
        return true;
    }

    private void insertAllocateEvent(Action a, UUID vm) {
        int prev = 0;
        if (rc.defined(vm)) {
            prev = rc.get(vm);
        }
        int now = 0;
        IntDomainVar nowI = getVMsAllocation(rp.getVM(vm));
        if (nowI != null) {
            now = nowI.getInf();
        }
        if (prev != now) {
            AllocateEvent ev = new AllocateEvent(vm, getResourceIdentifier(), now);
            a.addEvent(Action.Hook.pre, ev);
        }
    }

    private boolean insertAllocateAction(ReconfigurationPlan p, UUID vm, UUID destNode, int st) {
        String rcId = getResourceIdentifier();
        int prev = rc.get(vm);
        int now = getVMsAllocation()[rp.getVM(vm)].getVal();
        if (prev != now) {
            Allocate a = new Allocate(vm, destNode, rcId, now, st, st);
            return p.add(a);
        }
        return false;
    }

    /**
     * Symmetry breaking for VMs that stay running, on the same node.
     *
     * @return
     */
    private boolean symmetryBreakingForStatingVMs() {
        for (UUID vm : rp.getFutureRunningVMs()) {
            VMActionModel a = rp.getVMAction(vm);
            Slice dSlice = a.getDSlice();
            Slice cSlice = a.getCSlice();
            if (dSlice != null && cSlice != null) {
                IntDomainVar stay = ((KeepRunningVMModel) a).isStaying();

                if (getSourceResource().get(vm) <= getVMsAllocation(rp.getVM(vm)).getInf()) {
                    //If the resource usage will be increasing
                    //Then the duration of the dSlice can be set to 0
                    //(the allocation will be performed at the end of the reconfiguration process)
                    if (stay.isInstantiatedTo(1)) {
                        try {
                            dSlice.getDuration().setVal(0);
                        } catch (ContradictionException ex) {
                            rp.getLogger().info("Unable to set the dSlice duration of {} to 0", dSlice.getSubject());
                            return false;
                        }
                    } else {
                        solver.post(new FastImpliesEq(stay, dSlice.getDuration(), 0));
                    }

                } else {
                    //Else, the resource usage is decreasing, so
                    // we set the cSlice duration to 0 to directly reduce the resource allocation
                    if (stay.isInstantiatedTo(1)) {
                        try {
                            cSlice.getDuration().setVal(0);
                        } catch (ContradictionException ex) {
                            rp.getLogger().info("Unable to set the cSlice duration of {} to 0", cSlice.getSubject());
                            return false;
                        }
                    } else {
                        rp.getSolver().post(new FastImpliesEq(stay, cSlice.getDuration(), 0));
                    }
                }
            }
        }
        return true;
    }

    private boolean linkVirtualToPhysicalUsage() {
        for (int nIdx = 0; nIdx < ratios.length; nIdx++) {
            if (!linkVirtualToPhysicalUsage(nIdx)) {
                return false;
            }
        }

        //The slice scheduling constraint that is necessary
        //TODO: a slice on both the real and the raw resource usage ?
        TIntArrayList cUse = new TIntArrayList();
        List<IntDomainVar> dUse = new ArrayList<>();

        for (UUID vmId : rp.getVMs()) {
            VMActionModel a = rp.getVMAction(vmId);
            Slice c = a.getCSlice();
            Slice d = a.getDSlice();
            if (c != null) {
                cUse.add(getSourceResource().get(vmId));
            }
            if (d != null) {
                dUse.add(vmAllocation[rp.getVM(vmId)]);
            }
        }

        IntDomainVar[] capa = new IntDomainVar[rp.getNodes().length];
        System.arraycopy(virtRcUsage, 0, capa, 0, rp.getNodes().length);
        rp.getTaskSchedulerBuilder().add(capa, cUse.toNativeArray(), dUse.toArray(new IntDomainVar[dUse.size()]));
        return true;
    }

    private boolean linkVirtualToPhysicalUsage(int nIdx) {

        double r = ratios[nIdx].getSup();
        if (r == UNCHECKED_RATIO) {
            //Default overbooking ratio is 1.
            r = 1;
        }

        try {
            ratios[nIdx].intersect(new RealIntervalConstant(r, r));
        } catch (ContradictionException ex) {
            rp.getLogger().error("Unable to set '{}' to {}", ratios[nIdx], r);
            return false;
        }

        if (r == 1) {
            solver.post(solver.eq(phyRcUsage[nIdx], virtRcUsage[nIdx]));
            try {
                virtRcUsage[nIdx].setSup(phyRcUsage[nIdx].getSup());
            } catch (ContradictionException ex) {
                rp.getLogger().error("Unable to restrict the virtual '{}' capacity of {} to {}: ", rp.getNode(nIdx), phyRcUsage[nIdx].getSup(), ex.getMessage());
                return false;
            }
        } else {
            //beware of truncation made by choco: 3 = 7 / 2 while here, 4 pCPU will be used
            //The hack consists in computing the number of free pCPU
                /*
                int maxRaw = ...;
                int maxReal = maxRaw * factor;
                freeReal = var(0,maxReal)
                post(eq(freeReal, minus(maxReal,usageReal))
                freeRaw = div(freeReal,factor);
                eq(usageRaw, minus(maxRaw,freeRaw)
                 */
            //example: 6 pCPU, 7 vCPU, factor= 2
            //freePCpu = ((2 * 6) - 7) / 2 = 2
            //usedPCPU = 6 - 2 = 4 \o/
            int maxRaw = getSourceResource().get(rp.getNode(nIdx));
            int maxReal = (int) (maxRaw * r); //Truncation, we ignore partial virtual resource so it's correct
            try {
                virtRcUsage[nIdx].setSup(maxReal);
            } catch (ContradictionException ex) {
                rp.getLogger().error("Unable to restrict the virtual '{}' capacity of {} to {}: {}", getResourceIdentifier(), rp.getNode(nIdx), maxReal, ex.getMessage());
                return false;
            }
            IntDomainVar freeReal = solver.createBoundIntVar(rp.makeVarLabel("free_real('", rp.getNode(nIdx), "')"), 0, maxReal);
            solver.post(solver.eq(freeReal, CPSolver.minus(maxReal, virtRcUsage[nIdx])));
            IntDomainVar freeRaw = ChocoUtils.div(solver, freeReal, (int) r); //TODO: check for the correctness of the truncation
            solver.post(solver.eq(phyRcUsage[nIdx], CPSolver.minus(maxRaw, freeRaw)));
        }
        return true;

    }

}
