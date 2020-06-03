/*
 * Copyright  2020 The BtrPlace Authors. All rights reserved.
 * Use of this source code is governed by a LGPL-style
 * license that can be found in the LICENSE.txt file.
 */

package org.btrplace.scheduler.runner.disjoint.splitter;

import gnu.trove.map.hash.TIntIntHashMap;
import org.btrplace.model.Instance;
import org.btrplace.model.VM;
import org.btrplace.model.constraint.Root;

import java.util.List;

/**
 * Splitter for {@link org.btrplace.model.constraint.Root} constraints.
 * When the constraint focuses VMs among different partitions,
 * the constraint is split.
 * <p>
 * This operation is conservative wrt. the constraint semantic.
 *
 * @author Fabien Hermenier
 */
public class RootSplitter implements ConstraintSplitter<Root> {

    @Override
    public Class<Root> getKey() {
        return Root.class;
    }

    @Override
    public boolean split(Root cstr, Instance origin, final List<Instance> partitions, TIntIntHashMap vmsPosition, TIntIntHashMap nodePosition) {
        VM v = cstr.getInvolvedVMs().iterator().next();
        int i = vmsPosition.get(v.id());
        return partitions.get(i).getSatConstraints().add(cstr);
    }

}
