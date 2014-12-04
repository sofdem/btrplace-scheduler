/*
 * Copyright (c) 2014 University Nice Sophia Antipolis
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

package org.btrplace.safeplace.runner;

import net.minidev.json.JSONArray;
import net.minidev.json.JSONObject;
import org.btrplace.safeplace.Constraint;
import org.btrplace.safeplace.Specification;
import org.btrplace.safeplace.backend.NoDuplicatedStore;
import org.btrplace.safeplace.backend.ReducedDefiantStore;
import org.btrplace.safeplace.fuzzer.ReconfigurationPlanFuzzer2;
import org.btrplace.safeplace.guard.ErrorGuard;
import org.btrplace.safeplace.guard.MaxTestsGuard;
import org.btrplace.safeplace.guard.TimeGuard;
import org.btrplace.safeplace.reducer.ElementsReducer;
import org.btrplace.safeplace.reducer.PlanReducer;
import org.btrplace.safeplace.spec.SpecExtractor;
import org.btrplace.safeplace.verification.TestCase;
import org.btrplace.safeplace.verification.TestCaseConverter;
import org.btrplace.safeplace.verification.Verifier;
import org.btrplace.safeplace.verification.btrplace.CheckerVerifier;
import org.btrplace.safeplace.verification.btrplace.ImplVerifier;
import org.btrplace.safeplace.verification.spec.IntVerifDomain;
import org.btrplace.safeplace.verification.spec.StringEnumVerifDomain;
import org.btrplace.safeplace.verification.spec.VerifDomain;

import java.io.FileWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * @author Fabien Hermenier
 */
public class VerifyFuzz {

    private static String json = null;
    private static int verbosityLvl = 0;
    private static int nbWorkers = Runtime.getRuntime().availableProcessors() - 1;

    private static List<VerifDomain> vDoms = new ArrayList<>();

    private static void exit(String msg) {
        System.err.println(msg);
        System.exit(1);
    }

    private static Specification getSpec() throws Exception {
        SpecExtractor r = new SpecExtractor();
        return r.extract();
    }

    private static Verifier makeVerifier(String verifier) {
        switch (verifier) {
            case "impl":
                return new ImplVerifier();
            case "impl_repair":
                ImplVerifier v = new ImplVerifier();
                v.repair(true);
                return v;
            case "checker":
                return new CheckerVerifier();
        }
        exit("Unsupported verifier: '" + verifier);
        return null;
    }

    private static void serialize(NoDuplicatedStore b, String output) {
        Collection<TestCase> defiant = b.getDefiant();
        Collection<TestCase> compliant = b.getCompliant();
        TestCaseConverter tcc = new TestCaseConverter();
        if (output == null) {
            return;
        }
        try (FileWriter implF = new FileWriter(output)) {
            JSONArray arr = new JSONArray();
            for (TestCase tc : defiant) {
                JSONObject o = new JSONObject();
                o.put("tc", tcc.toJSON(tc));
                o.put("succeeded", false);
                arr.add(o);
            }
            for (TestCase tc : compliant) {
                JSONObject o = new JSONObject();
                o.put("tc", tcc.toJSON(tc));
                o.put("succeeded", true);
                arr.add(o);
            }
            arr.writeJSONString(implF);
        } catch (Exception e) {
            exit(e.getMessage());
        }
    }

    private static void makeVerifDomain(String def) {
        String[] toks = def.split("=");

        if (toks[0].equals("int")) {
            String[] bounds = toks[1].split("\\.\\.");
            vDoms.add(new IntVerifDomain(Integer.parseInt(bounds[0]), Integer.parseInt(bounds[1])));
        } else if (toks[0].equals("string")) {
            vDoms.add(new StringEnumVerifDomain(toks[1].split(",")));
        }
    }

    private static void usage() {
        System.out.println("Verify [options] cstr_id");
        System.out.println("\tVerify the constraint 'cstr_id'");
        System.out.println("\nOptions:");
        System.out.println("--verifier (impl | impl_repair | checker)\tthe verifier to compare to");
        System.out.println("--continuous perform a verification wrt. a continuous restriction (default)");
        System.out.println("--discrete perform a verification wrt. a discrete restriction");
        System.out.println("--size VxN\tmake a model of V vms and N nodes");
        System.out.println("--dom key=lb..ub. Search space for the given type");
        System.out.println("--durations min..sup\taction duration vary from min to sup (incl). Default is 1..3");
        System.out.println("--json out\tthe JSON file where failures are stored. Default is no output");
        System.out.println("-p nb\tNb. of verifications in parallel. Default is " + nbWorkers);
        System.out.println("-v Increment the verbosity level (up to three '-v').");
        System.out.println("-h | --help\tprint this help");
        System.exit(1);
    }

    public static void main(String[] args) throws Exception {
        //Parse arguments
        int i;
        boolean endOptions = false;
        String cstrId;

        /*
         spec cstr NxM verif options
         */
        cstrId = args[0];

        String[] ts = args[1].split("x");
        int nbVMs = Integer.parseInt(ts[0]);
        int nbNodes = Integer.parseInt(ts[1]);
        String verifier = args[2];


        ReconfigurationPlanFuzzer2 fuzz = null;
        fuzz = new ReconfigurationPlanFuzzer2();
        fuzz.nbNodes(nbNodes).nbVMs(nbVMs);

        final Specification spec = getSpec();
        final Constraint c = spec.get(cstrId);
        final Verifier v = makeVerifier(verifier);

        ParallelConstraintVerificationFuzz paraVerif = new ParallelConstraintVerificationFuzz(fuzz, vDoms, v, c);

        for (i = 4; i < args.length; i++) {
            String k = args[i];
            switch (k) {
                case "--continuous":
                    paraVerif.setContinuous(true);
                    break;
                case "--discrete":
                    paraVerif.setContinuous(false);
                    break;
                case "--dom":
                    makeVerifDomain(args[++i]);
                    break;
                case "--json":
                    json = args[++i];
                    break;
                case "-h":
                case "--help":
                    usage();
                    break;
                case "-p":
                    paraVerif.setNbWorkers(Integer.parseInt(args[++i]));
                    break;
                case "-v":
                    paraVerif.setVerbose(true);
                    verbosityLvl++;
                    break;
                case "-t":
                    paraVerif.limit(new TimeGuard(Integer.parseInt(args[++i])));
                    break;
                case "-f":
                    paraVerif.limit(new ErrorGuard(Integer.parseInt(args[++i])));
                    break;
                case "-m":
                    paraVerif.limit(new MaxTestsGuard(Integer.parseInt(args[++i])));
                    break;

                default:
                    System.err.println("Unsupported option: " + args[i]);
                    System.exit(1);
                    break;
            }
        }
        ReducedDefiantStore b = new ReducedDefiantStore();
        b.reduceWith(new PlanReducer());
        b.reduceWith(new ElementsReducer());
        paraVerif.setBackend(b);

        List<Constraint> pre = makePreconditions(c, spec);
        for (Constraint x : pre) {
            paraVerif.precondition(x);
        }
        try {
            paraVerif.verify();
        } catch (Exception ex) {
            if (ex.getMessage().contains("don't") || ex.getMessage().contains("discrete")) {
                System.err.println(ex.getMessage());
                if (verbosityLvl > 0) {
                    System.out.println("-/-/- failure(s)");
                }
                System.exit(-1);
            }
            exit(ex.getMessage());
        }


        int nbD = b.getNbDefiant();
        int nbC = b.getNbCompliant();
        int falseOk = 0, falseKo = 0;
        for (TestCase tc : b.getDefiant()) {
            if (tc.falseNegative()) {
                falseKo++;
            } else if (tc.falsePositive()) {
                falseOk++;
            } else {
                System.err.println("---BUG:\n" + tc.pretty(false));
            }
        }
        if (nbD != (falseKo + falseOk)) {
            System.err.println("BUG: " + nbD + " defiant but ok=" + falseOk + " and ko=" + falseKo);
            System.exit(1);
        }
        if (verbosityLvl > 0) {
            System.out.println(falseOk + "/" + falseKo + "/" + (nbD + nbC));
        }

        if (verbosityLvl > 1) {
            System.out.println("---- Defiant TestCases ----");
            for (TestCase tc : b.getDefiant()) {
                System.out.println(tc.pretty(true));
            }

            if (verbosityLvl > 2) {
                System.out.println("---- Compliant TestCases ----");
                for (TestCase tc : b.getCompliant()) {
                    System.out.println(tc.pretty(true));
                }
            }
        }
        serialize(b, json);
        System.exit(nbD);
    }

    private static List<Constraint> makePreconditions(Constraint c, Specification spec) {
        List<Constraint> pre = new ArrayList<>();
        for (Constraint x : spec.getConstraints()) {
            if (x.isCore()) {
                pre.add(x);
            }
        }

        //In case c is a core one, we still want to be able to verify it
        pre.remove(c);
        return pre;
    }
}