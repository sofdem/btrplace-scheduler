package btrplace.solver.api.cstrSpec.spec.type;

import btrplace.solver.api.cstrSpec.spec.term.Constant;

/**
 * @author Fabien Hermenier
 */
public class StringType extends Atomic {

    private static StringType instance = new StringType();

    @Override
    public boolean match(String n) {
        return true;
    }

    @Override
    public Constant newValue(String n) {
        if (match(n)) {
            return new Constant(n, this);
        }
        return null;
    }

    @Override
    public String label() {
        return "string";
    }

    @Override
    public String toString() {
        return label();
    }

    public static StringType getInstance() {
        return instance;
    }

    @Override
    public boolean comparable(Type t) {
        return t.equals(NoneType.getInstance()) || equals(t);
    }

}