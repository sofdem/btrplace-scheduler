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

package org.btrplace.plan;

import org.btrplace.model.Model;
import org.btrplace.plan.event.Action;

/**
 * An exception to notify an action is not feasible due to the current model state.
 *
 * @author Fabien Hermenier
 */
public class InfeasibleActionException extends RuntimeException {

    private final transient Model model;

    private final transient Action action;

    /**
     * New exception.
     *
     * @param model  the initial model
     * @param action the action that cannot be applied on the model
     */
    public InfeasibleActionException(Model model, Action action) {
        super("Action '" + action + "' cannot be applied on the following mode:\n" + model);
        this.action = action;
        this.model = model;
    }

    /**
     * Get the initial model.
     *
     * @return a model
     */
    public Model getModel() {
        return model;
    }

    /**
     * Get the action that is not applyable
     *
     * @return an action
     */
    public Action getAction() {
        return action;
    }
}
