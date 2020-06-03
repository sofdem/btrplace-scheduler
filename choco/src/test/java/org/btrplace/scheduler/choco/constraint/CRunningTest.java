/*
 * Copyright  2020 The BtrPlace Authors. All rights reserved.
 * Use of this source code is governed by a LGPL-style
 * license that can be found in the LICENSE.txt file.
 */

package org.btrplace.scheduler.choco.constraint;

import org.btrplace.model.DefaultModel;
import org.btrplace.model.Instance;
import org.btrplace.model.Model;
import org.btrplace.model.Node;
import org.btrplace.model.VM;
import org.btrplace.model.constraint.MinMTTR;
import org.btrplace.model.constraint.Running;
import org.testng.Assert;
import org.testng.annotations.Test;

import java.util.Collections;

/**
 * Unit tests for {@link org.btrplace.scheduler.choco.constraint.CRunning}.
 *
 * @author Fabien Hermenier
 */
public class CRunningTest {

    @Test
    public void testGetMisplaced() {
        Model mo = new DefaultModel();
        VM vm1 = mo.newVM();
        VM vm2 = mo.newVM();
        Node n1 = mo.newNode();
        mo.getMapping().on(n1).ready(vm1).run(n1, vm2);

        Instance i = new Instance(mo, Collections.emptyList(), new MinMTTR());
        CRunning k = new CRunning(new Running(vm1));
        Assert.assertEquals(1, k.getMisPlacedVMs(i).size());
        Assert.assertTrue(k.getMisPlacedVMs(i).contains(vm1));

        k = new CRunning(new Running(vm2));
        Assert.assertEquals(0, k.getMisPlacedVMs(i).size());
    }
}
