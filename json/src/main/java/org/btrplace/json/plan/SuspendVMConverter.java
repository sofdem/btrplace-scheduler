/*
 * Copyright (c) 2020 University Nice Sophia Antipolis
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

package org.btrplace.json.plan;

import net.minidev.json.JSONObject;
import org.btrplace.json.JSONConverterException;
import org.btrplace.json.JSONs;
import org.btrplace.model.Model;
import org.btrplace.plan.event.SuspendVM;

/**
 * JSON serialisation for {@link org.btrplace.plan.event.SuspendVM} actions.
 */
public class SuspendVMConverter implements ActionConverter<SuspendVM> {

  @Override
  public String id() {
    return "suspendVM";
  }

  @Override
  public Class<SuspendVM> supportedAction() {
    return SuspendVM.class;
  }

  @Override
  public void fillJSON(final SuspendVM ac, final JSONObject ob) {
    ob.put(VM_LABEL, JSONs.elementToJSON(ac.getVM()));
    ob.put(VM_DESTINATION_LABEL, JSONs.elementToJSON(ac.getDestinationNode()));
    ob.put(VM_LOCATION_LABEL, JSONs.elementToJSON(ac.getSourceNode()));
  }

  @Override
  public SuspendVM fromJSON(final Model mo, final JSONObject ob)
      throws JSONConverterException {

    return new SuspendVM(JSONs.requiredVM(mo, ob, VM_LABEL),
        JSONs.requiredNode(mo, ob, VM_LOCATION_LABEL),
        JSONs.requiredNode(mo, ob, VM_DESTINATION_LABEL),
        start(ob), end(ob));
  }
}
