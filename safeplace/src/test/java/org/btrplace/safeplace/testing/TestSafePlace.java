/*
 * Copyright (c) 2017 University Nice Sophia Antipolis
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

package org.btrplace.safeplace.testing;

import org.btrplace.safeplace.spec.Constraint;
import org.btrplace.safeplace.spec.SpecScanner;
import org.btrplace.safeplace.testing.fuzzer.Restriction;
import org.btrplace.safeplace.testing.fuzzer.decorators.ShareableResourceFuzzer;
import org.testng.Assert;

import java.util.EnumSet;
import java.util.List;

import static org.testng.Assert.assertEquals;

/**
 * @author Fabien Hermenier
 */
public class TestSafePlace {

    //Core constraints
    @CstrTest(groups = {"core"})
    public void testNoVmsOnOfflineNodes(TestCampaign c) {
        c.check("noVMsOnOfflineNodes")
                .vms(1)
                .nodes(1)
                .srcOffNodes(0.1)
                .srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure); 
    }

    @CstrTest(groups = {"core"})
    public void testToRunning(TestCampaign c) {
        c.check("toRunning").vms(1).nodes(1).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);
    }

    @CstrTest(groups = {"core"})
    public void testToSleeping(TestCampaign c) {
        c.check("toSleeping").vms(1).nodes(1).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);
    }

    @CstrTest(groups = {"core"})
    public void testToReady(TestCampaign c) {
        c.check("toReady").vms(1).nodes(1).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);
    }


    @CstrTest()
    public void testSpread(TestCampaign c) {
        c.check("spread").vms(10).nodes(3).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);
    }

    @CstrTest()
    public void testLonely(TestCampaign c) {
        c.check("lonely").vms(10).nodes(3).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);
    }

    @CstrTest()
    public void testGather(TestCampaign c) {
        c.check("gather").vms(10).nodes(3).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);
    }

    @CstrTest
    public void testBan(TestCampaign c) {
        c.check("ban").vms(10).nodes(3).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);
    }

    @CstrTest()
    public void testFence(TestCampaign c) {
        c.check("fence").vms(10).nodes(3).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);
    }

    @CstrTest()
    public void testAmong(TestCampaign c) {
        c.check("among").vms(10).nodes(3).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);
    }

    @CstrTest()
    public void testRoot(TestCampaign c) {
        c.check("root").vms(10).nodes(3).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);
    }

    @CstrTest()
    public void testSplit(TestCampaign c) {
        c.check("split").vms(10).nodes(3).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);
    }

    @CstrTest()
    public void testQuarantine(TestCampaign c) {
        c.check("quarantine").vms(10).nodes(3).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);
    }

    @CstrTest()
    public void testMaxOnline(TestCampaign c) {
        c.check("maxOnline").vms(10).nodes(3).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);
    }

    @CstrTest()
    public void testRunningCapacity(TestCampaign c) {
        c.check("runningCapacity").vms(10).nodes(3).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);
    }

    @CstrTest()
    public void testRunning(TestCampaign c) {
        c.check("running").vms(10).nodes(3).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);
    }

    @CstrTest()
    public void testSleeping(TestCampaign c) {
        c.check("sleeping").vms(10).nodes(3).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);
    }

    @CstrTest()
    public void testReady(TestCampaign c) {
        c.check("ready").vms(10).nodes(3).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);

    }

    @CstrTest()
    public void testOnline(TestCampaign c) {
        c.check("ONLINE").vms(10).nodes(3).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);
    }

    @CstrTest()
    public void testOffline(TestCampaign c) {
        c.check("offline").vms(10).nodes(3).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);
    }


    @CstrTest
    public void testResource(TestCampaign c) {
        c.check("shareableResource")
                .with("id", "cpu")
                .with(new ShareableResourceFuzzer("cpu", 1, 5, 10, 20).variability(0.5))
                .vms(10).nodes(3).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);
    }

    @CstrTest(groups = {"resourceCapacity"})
    public void testResourceCapacity(TestCampaign c) {
        c.check("resourceCapacity")
                .restriction(EnumSet.of(Restriction.CONTINUOUS, Restriction.DISCRETE))
                .with("id", "cpu")
                .with("qty", 1, 50)
                .with(new ShareableResourceFuzzer("cpu", 1, 5, 10, 20).variability(0.5))
                .vms(10).nodes(3).srcOffNodes(0.1).srcVMs(1, 9, 0);
        c.limits().tests(100).failures(1);
        //c.onDefect(DefectHooks.testNgFailure);
    }

    //@Test
    public void launcher() throws Exception {
        SpecScanner specScanner = new SpecScanner();
        List<Constraint> l = specScanner.scan();
        TestScanner sc = new TestScanner(l);
        List<TestCampaign> campaigns = sc.testGroups("resourceCapacity");
        if (campaigns.isEmpty()) {
            Assert.fail("Nothing to test");
        }
        assertEquals(campaigns.stream().mapToInt(tc -> {
            tc.schedulerParams().doRepair(false);
            return tc.go().defects();
        }).sum(), 0);

    }
}
