/*
 * Copyright (c) Fabien Hermenier
 *
 *        This file is part of Entropy.
 *
 *        Entropy is free software: you can redistribute it and/or modify
 *        it under the terms of the GNU Lesser General Public License as published by
 *        the Free Software Foundation, either version 3 of the License, or
 *        (at your option) any later version.
 *
 *        Entropy is distributed in the hope that it will be useful,
 *        but WITHOUT ANY WARRANTY; without even the implied warranty of
 *        MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *        GNU Lesser General Public License for more details.
 *
 *        You should have received a copy of the GNU Lesser General Public License
 *        along with Entropy.  If not, see <http://www.gnu.org/licenses/>.
 */

package btrplace.plan.actions;

import btrplace.model.Mapping;
import btrplace.model.Model;
import btrplace.plan.Action;

import java.util.UUID;

/**
 * Create a VM that will be able to be booted after. The action may be
 * a standalone action, or attached to a boot action in the same plan.
 * <p/>
 * If it is standalone, then the VM is not a part of the source configuration
 * will be in the waiting state at the end of the reconfiguration.
 * Otherwise, the VM is not a part of the source configuration and will be
 * in the running state at the end of the reconfiguration.
 *
 * @author Fabien Hermenier
 */
public class Instantiate extends Action {

    private UUID id;

    /**
     * Make a new action.
     *
     * @param vm the VM to instantiate.
     */
    public Instantiate(UUID vm, int st, int ed) {
        super(st, ed);
        this.id = vm;
    }

    @Override
    public boolean apply(Model m) {
        Mapping map = m.getMapping();

        if (!map.getAllVMs().contains(id)) {
            map.addWaitingVM(id);
            return true;
        }
        //Because a run action may have insert the VM before. Not nice but still...
        return map.getRunningVMs().contains(id);
    }

    /**
     * Test if this action is equals to another object.
     *
     * @param o the object to compare with
     * @return true if ref is an instance of Instantiate and if both
     *         instance involve the same virtual machine
     */
    @Override
    public boolean equals(Object o) {
        if (o == null) {
            return false;
        } else if (o == this) {
            return true;
        } else if (o.getClass() == this.getClass()) {
            Instantiate that = (Instantiate) o;
            return this.id.equals(that.id);
        }
        return false;
    }

    @Override
    public int hashCode() {
        int res = getEnd();
        res = getStart() + 31 * res;
        return id.hashCode() + 31 * res;
    }

    /**
     * Get the VM to instantiate.
     *
     * @return the VM identifier
     */
    public UUID getVM() {
        return id;
    }

    @Override
    public String toString() {
        return new StringBuilder("instantiate(").append(id).append(')').toString();
    }
}
