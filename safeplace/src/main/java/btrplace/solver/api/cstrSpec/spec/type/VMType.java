package btrplace.solver.api.cstrSpec.spec.type;

import btrplace.solver.api.cstrSpec.spec.term.Constant;

/**
 * @author Fabien Hermenier
 */
public class VMType extends Atomic {

    private static VMType instance = new VMType();

    private VMType() {
    }

    public static VMType getInstance() {
        return instance;
    }

    @Override
    public String toString() {
        return label();
    }

    @Override
    public boolean match(String n) {
        return false;
    }

    @Override
    public String label() {
        return "vm";
    }


    @Override
    public Constant newValue(String n) {
        throw new RuntimeException();
    }

    @Override
    public boolean comparable(Type t) {
        return t.equals(NoneType.getInstance()) || equals(t);
    }

}