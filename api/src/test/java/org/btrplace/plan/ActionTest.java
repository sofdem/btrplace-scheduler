/*
 * Copyright  2020 The BtrPlace Authors. All rights reserved.
 * Use of this source code is governed by a LGPL-style
 * license that can be found in the LICENSE.txt file.
 */

package org.btrplace.plan;

import org.btrplace.model.DefaultModel;
import org.btrplace.model.Model;
import org.btrplace.model.VM;
import org.btrplace.plan.event.Action;
import org.btrplace.plan.event.Event;
import org.testng.Assert;
import org.testng.annotations.Test;

import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

/**
 * Unit tests for {@link org.btrplace.plan.event.Action}.
 *
 * @author Fabien Hermenier
 */
public class ActionTest {

    @Test
    public void testBasics() {
        Action a1 = new MockAction(new VM(1), 1, 3);
        Assert.assertEquals(1, a1.getStart());
        Assert.assertEquals(3, a1.getEnd());
        Assert.assertTrue(a1.getEvents(Action.Hook.PRE).isEmpty());
        Assert.assertTrue(a1.getEvents(Action.Hook.POST).isEmpty());
    }

    @Test
    public void testEvents() {
        Action a1 = new MockAction(new VM(1), 1, 3);
        Event e = mock(Event.class);
        Assert.assertTrue(a1.addEvent(Action.Hook.PRE, e));
        Assert.assertFalse(a1.addEvent(Action.Hook.PRE, e));
        Assert.assertEquals(1, a1.getEvents(Action.Hook.PRE).size());
        a1.addEvent(Action.Hook.POST, e);
        Assert.assertEquals(1, a1.getEvents(Action.Hook.POST).size());
        Event e2 = mock(Event.class);
        a1.addEvent(Action.Hook.POST, e2);
        Assert.assertEquals(2, a1.getEvents(Action.Hook.POST).size());
        String str = a1.toString();
        // Check for issue #203. Only one occurrence of the event is reported.
        Assert.assertEquals(str.indexOf(String.valueOf(e2.hashCode())), str.lastIndexOf(String.valueOf(e2.hashCode())));
    }

    @Test
    public void testApply() {
        Model mo = new DefaultModel();

        MockAction a1 = new MockAction(new VM(1), 1, 3);
        Event e = mock(Event.class);
        when(e.apply(mo)).thenReturn(true);
        a1.addEvent(Action.Hook.PRE, e);
        a1.addEvent(Action.Hook.POST, e);

        a1.apply(mo);

        verify(e, times(2)).apply(mo);
        Assert.assertEquals(a1.count, 1);
    }
}
