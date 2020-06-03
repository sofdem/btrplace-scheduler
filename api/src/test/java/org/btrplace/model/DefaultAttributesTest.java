/*
 * Copyright  2020 The BtrPlace Authors. All rights reserved.
 * Use of this source code is governed by a LGPL-style
 * license that can be found in the LICENSE.txt file.
 */

package org.btrplace.model;

import org.testng.Assert;
import org.testng.annotations.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

/**
 * Unit tests for {@link DefaultAttributes}.
 *
 * @author Fabien Hermenier
 */
public class DefaultAttributesTest {

  private static final Model mo = new DefaultModel();
  private static final List<VM> vms = Util.newVMs(mo, 10);
  private static final List<Node> nodes = Util.newNodes(mo, 10);

  @Test
  public void testInstantiation() {
    Attributes attrs = new DefaultAttributes();
    Assert.assertFalse(attrs.toString().contains("null"));
    Assert.assertTrue(attrs.getDefined().isEmpty());
  }


  @Test(dependsOnMethods = {"testInstantiation"})
    public void testPutAndGetString() {
        Attributes attrs = new DefaultAttributes();

        Assert.assertFalse(attrs.put(vms.get(0), "foo", "bar"));
        Assert.assertEquals(attrs.get(vms.get(0), "foo", ""), "bar");
        Assert.assertTrue(attrs.put(vms.get(0), "foo", "baz"));
        Assert.assertEquals(attrs.get(vms.get(0), "foo", ""), "baz");

        Assert.assertEquals(attrs.get(vms.get(0), "__", "++"), "++");
    }


    @Test(dependsOnMethods = {"testInstantiation"})
    public void testPutAndGetDouble() {
        Attributes attrs = new DefaultAttributes();

        Assert.assertFalse(attrs.put(vms.get(0), "foo", 17.3));
        Assert.assertEquals(attrs.get(vms.get(0), "foo", 8.5), 17.3);
        Assert.assertEquals(attrs.get(vms.get(0), "fiz", 8.5), 8.5);
    }

    @Test(dependsOnMethods = {"testInstantiation"})
    public void testPutAndGetBoolean() {
        Attributes attrs = new DefaultAttributes();

        Assert.assertFalse(attrs.put(vms.get(0), "foo", true));
        Assert.assertEquals(attrs.get(vms.get(0), "foo", false), true);
        Assert.assertTrue(attrs.put(vms.get(0), "foo", false));
        Assert.assertEquals(attrs.get(vms.get(0), "foo", true), false);
        Assert.assertEquals(attrs.get(vms.get(0), "__", true), true);
    }

    @Test(dependsOnMethods = {"testInstantiation"})
    public void testCastAndPut() {
        DefaultAttributes attrs = new DefaultAttributes();

        attrs.castAndPut(vms.get(0), "foo", "foo");
        Assert.assertEquals(attrs.get(vms.get(0), "foo").getClass(), String.class);
        attrs.castAndPut(vms.get(0), "foo", "true");
        Assert.assertEquals(attrs.get(vms.get(0), "foo").getClass(), Boolean.class);

        attrs.castAndPut(vms.get(0), "foo", "false");
        Assert.assertEquals(attrs.get(vms.get(0), "foo").getClass(), Boolean.class);

        attrs.castAndPut(vms.get(0), "foo", "True");
        Assert.assertEquals(attrs.get(vms.get(0), "foo").getClass(), Boolean.class);

        attrs.castAndPut(vms.get(0), "foo", "135");
        Assert.assertEquals(attrs.get(vms.get(0), "foo").getClass(), Integer.class);

        attrs.castAndPut(vms.get(0), "foo", "13.56");
        Assert.assertEquals(attrs.get(vms.get(0), "foo").getClass(), Double.class);
    }

    @Test(dependsOnMethods = {"testPutAndGetString", "testInstantiation"})
    public void testIsSet() {
        Attributes attrs = new DefaultAttributes();
        Assert.assertFalse(attrs.isSet(vms.get(0), "foo"));
        attrs.put(vms.get(0), "foo", "bar");
        Assert.assertTrue(attrs.isSet(vms.get(0), "foo"));

    }

    @Test(dependsOnMethods = {"testPutAndGetString", "testInstantiation"})
    public void testUnset() {
        Attributes attrs = new DefaultAttributes();

        Assert.assertFalse(attrs.unset(vms.get(0), "foo"));
        attrs.put(vms.get(0), "foo", "bar");
        Assert.assertTrue(attrs.unset(vms.get(0), "foo"));
        Assert.assertFalse(attrs.isSet(vms.get(0), "foo"));
        Assert.assertFalse(attrs.unset(vms.get(0), "foo"));
    }

    @Test(dependsOnMethods = {"testInstantiation", "testUnset"})
    public void testClone() {
        Attributes attrs = new DefaultAttributes();
        List<Node> l = new ArrayList<>();
        for (int i = 0; i < 5; i++) {
            Node u = mo.newNode();
            attrs.put(u, Integer.toString(i), i);
            l.add(u);
        }
        Attributes attrs2 = attrs.copy();

        attrs.unset(l.get(0), "0");
        Assert.assertEquals(attrs2.get(l.get(0), "0", -1), 0);

        attrs2.unset(l.get(1), "1");
        Assert.assertEquals(attrs.get(l.get(1), "1", -2), 1);
    }

    @Test(dependsOnMethods = {"testInstantiation", "testUnset", "testClone"})
    public void testEqualsHashCode() {
        Attributes attrs = new DefaultAttributes();
        for (int i = 0; i < 5; i++) {
            attrs.put(nodes.get(0), Integer.toString(i), i);
            attrs.put(vms.get(0), Integer.toString(i), i);
        }
        Assert.assertTrue(attrs.equals(attrs));
        Attributes attrs2 = attrs.copy();
        Assert.assertTrue(attrs2.equals(attrs));
        Assert.assertTrue(attrs.equals(attrs));
        Assert.assertEquals(attrs.hashCode(), attrs2.hashCode());
        attrs.unset(nodes.get(0), "0");
        Assert.assertFalse(attrs2.equals(attrs));
        Assert.assertFalse(attrs.equals(attrs2));
        Assert.assertNotSame(attrs.hashCode(), attrs2.hashCode());
    }

    @Test(dependsOnMethods = {"testInstantiation"})
    public void testClear() {
        Attributes attrs = new DefaultAttributes();
        for (int i = 0; i < 5; i++) {
            attrs.put(nodes.get(i), Integer.toString(i), i);
            attrs.put(vms.get(i), Integer.toString(i), i);
        }
        attrs.clear();
        Assert.assertTrue(attrs.getDefined().isEmpty());
        attrs.put(nodes.get(0), "foo", true);
        attrs.put(vms.get(0), "bar", true);
        attrs.clear(nodes.get(0));
        Assert.assertTrue(attrs.isSet(vms.get(0), "bar"));
        Assert.assertFalse(attrs.isSet(nodes.get(0), "foo"));
        attrs.clear(vms.get(0));
        Assert.assertFalse(attrs.isSet(vms.get(0), "bar"));

    }

    @Test
    public void testGetKeys() {
        Attributes attrs = new DefaultAttributes();
        VM u = vms.get(0);
        attrs.put(u, "foo", 1);
        attrs.put(u, "bar", 1);
        Set<String> s = attrs.getKeys(u);
        Assert.assertEquals(s.size(), 2);
        Assert.assertTrue(s.containsAll(Arrays.asList("foo", "bar")));
        Assert.assertEquals(attrs.getKeys(mo.newVM()).size(), 0);
        Assert.assertEquals(attrs.getKeys(mo.newNode()).size(), 0);
    }
}
