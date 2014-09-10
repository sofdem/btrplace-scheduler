package btrplace.solver.api.cstrSpec.spec.prop;

import btrplace.solver.api.cstrSpec.spec.term.Term;
import btrplace.solver.api.cstrSpec.verification.spec.SpecModel;

import java.util.Collection;

/**
 * @author Fabien Hermenier
 */
public class Inc extends AtomicProp {

    public Inc(Term a, Term b) {
        super(a, b, "<:");
    }

    @Override
    public AtomicProp not() {
        return new NInc(a, b);
    }

    @Override
    public Boolean eval(SpecModel m) {
        Collection o = (Collection) a.eval(m);
        Collection c = (Collection) b.eval(m);
        if (o != null && c != null) {
            return c.containsAll(o);
        }
        return null;
    }

}