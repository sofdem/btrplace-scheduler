/*
 * Copyright  2020 The BtrPlace Authors. All rights reserved.
 * Use of this source code is governed by a LGPL-style
 * license that can be found in the LICENSE.txt file.
 */

package org.btrplace.btrpsl.constraint;

import org.btrplace.btrpsl.ScriptBuilder;
import org.btrplace.btrpsl.ScriptBuilderException;
import org.btrplace.model.DefaultModel;
import org.btrplace.model.Node;
import org.btrplace.model.constraint.Overbook;
import org.btrplace.model.constraint.SatConstraint;
import org.testng.Assert;
import org.testng.annotations.DataProvider;
import org.testng.annotations.Test;

import java.util.HashSet;
import java.util.Set;

/**
 * Unit tests for {@link OverbookBuilder}.
 *
 * @author Fabien Hermenier
 */
@Test
public class OverbookBuilderTest {

    @DataProvider(name = "badOverbooks")
    public Object[][] getBadSignatures() {
        return new String[][]{
                new String[]{"overbook({@N1,@N2},-1);"},
                new String[]{"overbook(\"foo\",-1);"},
                new String[]{">>overbook({},5);"},
                new String[]{"overbook(@N[1,3,5]);"},
                new String[]{">>overbook(@N[1,3,5,15],\"foo\");"},
                new String[]{"overbook(5);"},
        };
    }

    @Test(dataProvider = "badOverbooks", expectedExceptions = {ScriptBuilderException.class})
    public void testBadSignatures(String str) throws ScriptBuilderException {
        ScriptBuilder b = new ScriptBuilder(new DefaultModel());
        try {
            b.build("namespace test; VM[1..10] : tiny;\n@N[1..20] : defaultNode;\n" + str);
        } catch (ScriptBuilderException ex) {
            System.out.println(str + " " + ex.getMessage());
            throw ex;
        }
    }

    @DataProvider(name = "goodOverbooks")
    public Object[][] getGoodSignatures() {
        return new Object[][]{
                new Object[]{">>overbook(@N1,\"foo\",3);", 1, "foo", 3},
                new Object[]{"overbook(@N[1..4],\"bar\", 7.5);", 4, "bar", 7.5},
        };
    }

    @Test(dataProvider = "goodOverbooks")
    public void testGoodSignatures(String str, int nbNodes, String rcId, double ratio) throws Exception {
        ScriptBuilder b = new ScriptBuilder(new DefaultModel());
        Set<SatConstraint> cstrs = b.build("namespace test; VM[1..10] : tiny;\n@N[1..20] : defaultNode;\n" + str).getConstraints();
        Assert.assertEquals(cstrs.size(), nbNodes);
        Set<Node> nodes = new HashSet<>();
        for (SatConstraint s : cstrs) {
            Assert.assertTrue(s instanceof Overbook);
            Assert.assertTrue(nodes.addAll(s.getInvolvedNodes()));
            Assert.assertEquals(s.getInvolvedNodes().size(), 1);
            Assert.assertEquals(((Overbook) s).getResource(), rcId);
            Assert.assertEquals(((Overbook) s).getRatio(), ratio);
            Assert.assertEquals(s.isContinuous(), !str.startsWith(">>"));

        }
    }
}
