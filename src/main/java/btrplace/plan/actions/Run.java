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
package btrplace.plan.actions;


import btrplace.model.Model;
import btrplace.plan.Action;

import java.util.UUID;

/**
 * An action that demand to run a virtual machine on an online node. The virtual machine comes to the state "running" for "waiting".
 *
 * @author Fabien Hermenier
 */
public class Run extends Action {

    private UUID vm;

    private UUID node;

    /**
     * Make a new time-bounded run.
     *
     * @param vm  the virtual machine to run
     * @param to  the destination node
     * @param st  the moment the action starts.
     * @param end the moment the action finish
     */
    public Run(UUID vm, UUID to, int st, int end) {
        super(st, end);
        this.vm = vm;
        this.node = to;
    }

    /**
     * Textual representation of the action.
     *
     * @return a String
     */
    @Override
    public String toString() {
        return new StringBuilder("run(")
                .append(vm)
                .append(',')
                .append(node).append(')').toString();
    }

    @Override
    public boolean apply(Model c) {
        return c.getMapping().setVMRunOn(vm, node);
    }

    /**
     * Test if this action is equals to another object.
     *
     * @param o the object to compare with
     * @return true if ref is an instanceof Run and if both
     *         instance involve the same virtual machine and the same nodes
     */
    @Override
    public boolean equals(Object o) {
        if (o == null) {
            return false;
        } else if (o == this) {
            return true;
        } else if (o.getClass() == this.getClass()) {
            Run that = (Run) o;
            return this.vm.equals(that.vm) &&
                    this.node.equals(that.node) &&
                    this.getStart() == that.getStart() &&
                    this.getEnd() == that.getEnd();
        }
        return false;
    }

    @Override
    public int hashCode() {
        int res = getEnd();
        res = getStart() + 31 * res;
        res = vm.hashCode() + 31 * res;
        return 31 * res + node.hashCode();
    }
}
