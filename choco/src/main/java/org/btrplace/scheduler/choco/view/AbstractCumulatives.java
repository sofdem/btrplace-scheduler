/*
 * Copyright (c) 2016 University Nice Sophia Antipolis
 *
 * This file is part of btrplace.
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 3 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.btrplace.scheduler.choco.view;

import org.btrplace.model.VM;
import org.btrplace.scheduler.SchedulerException;
import org.btrplace.scheduler.choco.Parameters;
import org.btrplace.scheduler.choco.ReconfigurationProblem;
import org.btrplace.scheduler.choco.Slice;
import org.btrplace.scheduler.choco.extensions.LocalTaskScheduler;
import org.btrplace.scheduler.choco.transition.VMTransition;
import org.chocosolver.solver.variables.IntVar;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Basic for scheduling constraints related to resource management.
 *
 * @author Fabien Hermenier
 */
public abstract class AbstractCumulatives implements ChocoView {

    protected List<int[]> cUsages;

    protected List<IntVar[]> dUsages;

    protected int[] associations;

    protected IntVar[] cEnds;

    protected IntVar[] cHosts;

    protected IntVar[] dHosts;

    protected IntVar[] dStarts;

    /**
     * Ids of non-overlapping slices.
     */
    protected Map<VM, int[]> non;

    @Override
    public boolean inject(Parameters ps, ReconfigurationProblem rp) throws SchedulerException {
        cUsages = new ArrayList<>();
        dUsages = new ArrayList<>();

        List<Slice> dS = new ArrayList<>();
        List<Slice> cS = new ArrayList<>();


        non = new HashMap<>();

        int dIdx = 0;
        int cIdx = 0;

        for (VMTransition a : rp.getVMActions()) {
            Slice c = a.getCSlice();
            Slice d = a.getDSlice();

            if (d != null && c != null) {
                non.put(a.getVM(), new int[]{dIdx, cIdx});
            }
            if (d != null) {
                dS.add(dIdx, d);
                dIdx++;
            }

            if (c != null) {
                cS.add(cIdx, c);
                cIdx++;
            }
        }

        int i = 0;
        cHosts = new IntVar[cS.size()];
        cEnds = new IntVar[cS.size()];
        for (Slice s : cS) {
            cHosts[i] = s.getHoster();
            cEnds[i] = s.getEnd();
            i++;

        }

        i = 0;
        dStarts = new IntVar[dS.size()];
        dHosts = new IntVar[dS.size()];

        for (Slice s : dS) {
            dHosts[i] = s.getHoster();
            dStarts[i] = s.getStart();
            i++;
        }

        associations = makeAssociations();
        return true;
    }

    private int[] makeAssociations() {
        int[] res = new int[dHosts.length];
        //No associations task by default, then we create the associations.
        for (int i = 0; i < res.length; i++) {
            res[i] = LocalTaskScheduler.NO_ASSOCIATIONS;
        }
        for (Map.Entry<VM, int[]> e : non.entrySet()) {
            int[] assoc = e.getValue();
            res[assoc[0]] = assoc[1];
        }
        return res;
    }
}
