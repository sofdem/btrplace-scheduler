/*
 * Copyright  2020 The BtrPlace Authors. All rights reserved.
 * Use of this source code is governed by a LGPL-style
 * license that can be found in the LICENSE.txt file.
 */

package org.btrplace.btrpsl;

import org.btrplace.btrpsl.element.BtrpNumber;
import org.testng.Assert;
import org.testng.annotations.Test;

/**
 * Unit tests for SymbolsTable
 *
 * @author Fabien Hermenier
 */
@Test
public class SymbolsTableTest {

    public void testDeclare() {
        SymbolsTable t = new SymbolsTable();

        BtrpNumber i = new BtrpNumber(5, BtrpNumber.Base.BASE_10);
        t.declareImmutable("$v3", i);


        BtrpNumber i3 = new BtrpNumber(5, BtrpNumber.Base.BASE_10);
        Assert.assertTrue(t.declare("$v1", i3));
        Assert.assertEquals(t.getSymbol("$v1"), i3);
        Assert.assertTrue(t.isDeclared("$v1"));

        //Declared as immutable, no way
        Assert.assertFalse(t.declare("$v3", i));

        BtrpNumber i2 = new BtrpNumber(7, BtrpNumber.Base.BASE_10);
        Assert.assertTrue(t.declare("$v1", i2));
        Assert.assertEquals(t.getSymbol("$v1"), i2);

        Assert.assertNotNull(t.toString());
    }

    public void testDeclareImmutable() {
        SymbolsTable t = new SymbolsTable();

        BtrpNumber i = new BtrpNumber(5, BtrpNumber.Base.BASE_10);
        Assert.assertTrue(t.declareImmutable("$v1", i));
        Assert.assertEquals(t.getSymbol("$v1"), i);
        Assert.assertTrue(t.isDeclared("$v1"));
        Assert.assertTrue(t.isImmutable("$v1"));

        //No way to override an immutable value
        BtrpNumber i2 = new BtrpNumber(7, BtrpNumber.Base.BASE_10);
        Assert.assertFalse(t.declare("$v1", i2));
        Assert.assertFalse(t.declareImmutable("$v1", i2));

        Assert.assertNotNull(t.toString());
    }

    public void testRemove() {
        SymbolsTable t = new SymbolsTable();

        BtrpNumber i = new BtrpNumber(5, BtrpNumber.Base.BASE_10);
        t.declareImmutable("$v1", i);

        BtrpNumber i2 = new BtrpNumber(7, BtrpNumber.Base.BASE_10);
        t.declare("$v2", i2);

        Assert.assertNotNull(t.toString());

        Assert.assertTrue(t.remove("$v1"));
        Assert.assertTrue(t.remove("$v2"));
        Assert.assertFalse(t.remove("$v3"));
    }

    public void testPushAndPop() {
        SymbolsTable t = new SymbolsTable();

        BtrpNumber i = new BtrpNumber(5, BtrpNumber.Base.BASE_10);
        t.declareImmutable("$v1", i);

        BtrpNumber i2 = new BtrpNumber(7, BtrpNumber.Base.BASE_10);
        t.declare("$v2", i2);

        t.pushTable();
        Assert.assertTrue(t.isDeclared("$v1"));
        Assert.assertTrue(t.isDeclared("$v2"));

        BtrpNumber i3 = new BtrpNumber(7, BtrpNumber.Base.BASE_10);
        t.declare("$v3", i3);

        //New variable
        Assert.assertTrue(t.isDeclared("$v3"));

        //Redefinition
        BtrpNumber i4 = new BtrpNumber(-7, BtrpNumber.Base.BASE_10);
        t.declare("$v2", i4);
        Assert.assertEquals(t.getSymbol("$v2"), i4);

        //Immutable variable that will stay
        BtrpNumber i10 = new BtrpNumber(10, BtrpNumber.Base.BASE_10);
        t.declareImmutable("$v10", i10);


        Assert.assertTrue(t.popTable());
        //$v3 as disappear
        Assert.assertFalse(t.isDeclared("$v3"));
        Assert.assertNull(t.getSymbol("$v3"));

        //$v4 always present with the modified value
        Assert.assertEquals(t.getSymbol("$v2"), i4);

        Assert.assertEquals(t.getSymbol("$v10"), i10);

        Assert.assertFalse(t.popTable());


    }
}
