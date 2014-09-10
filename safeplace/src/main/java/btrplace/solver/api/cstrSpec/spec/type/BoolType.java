package btrplace.solver.api.cstrSpec.spec.type;

import btrplace.solver.api.cstrSpec.spec.term.Constant;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * @author Fabien Hermenier
 */
public class BoolType extends Atomic {

    public static final Set<Boolean> DOMAIN = Collections.unmodifiableSet(new HashSet<>(Arrays.asList(Boolean.TRUE, Boolean.FALSE)));

    private static BoolType instance = new BoolType();

    private BoolType() {
    }

    public static BoolType getInstance() {
        return instance;
    }

    @Override
    public String toString() {
        return label();
    }

    @Override
    public boolean match(String n) {
        return n.equalsIgnoreCase("true") || n.equalsIgnoreCase("false");
    }

    @Override
    public String label() {
        return "bool";
    }

    @Override
    public Constant newValue(String n) {
        return new Constant(Boolean.parseBoolean(n), BoolType.getInstance());
    }

    public Constant newValue(boolean i) {
        return new Constant(i, BoolType.getInstance());
    }

    @Override
    public boolean comparable(Type t) {
        return t.equals(NoneType.getInstance()) || equals(t);
    }
}