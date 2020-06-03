/*
 * Copyright  2020 The BtrPlace Authors. All rights reserved.
 * Use of this source code is governed by a LGPL-style
 * license that can be found in the LICENSE.txt file.
 */

package org.btrplace.scheduler.choco.runner;

import org.btrplace.model.Instance;
import org.btrplace.plan.ReconfigurationPlan;
import org.btrplace.scheduler.choco.Parameters;

import java.util.List;

/**
 * Simple interface to get statistics about a solving process.
 *
 * @author Fabien Hermenier
 */
public interface SolvingStatistics {

    /**
     * Get the solved instance.
     * @return the instance
     */
    Instance getInstance();

    /**
     * Get the time that was necessary to build the core-RP.
     *
     * @return a duration in milliseconds.  -1 if not available
     */
    long getCoreBuildDuration();

    /**
     * Get the time that was necessary to specialize the core-CP.
     *
     * @return a duration in milliseconds.  -1 if not available
     */
    long getSpecializationDuration();

    /**
     * Get the moment the computation starts.
     *
     * @return a time period in the epoch format
     */
    long getStart();

    /**
     * Get all the computed solutions ordered by time.
     *
     * @return a list of solutions that may be empty
     */
    List<SolutionStatistics> getSolutions();

    /**
     * Get the number of VMs managed by the algorithm.
     *
     * @return a positive number.  -1 if not available
     */
    int getNbManagedVMs();

    /**
     * Get the parameters of the scheduler.
     *
     * @return a set of parameters
     */
    Parameters getParameters();

    /**
     * Get the metrics related to the solving phase
     * @return metrics. {@code null} if the solver did not run
     */
    Metrics getMetrics();

    /**
     * Check if the solver completed the search.
     *
     * @return {@code true} indicates the solver proved the optimality of the computed solution or that the problem is
     * not feasible (if no solution were computed)
     */
    boolean completed();

    /**
     * Get the last computed reconfiguration plan.
     *
     * @return a plan. {@code null} if there was no solution
     */
    ReconfigurationPlan lastSolution();

    /**
     * Summarizes as a CSV data.
     * Print the statistics as a CSV line.
     * Fields are separated by a ';' and ordered this way:
     * - getNbManagedVMs()
     * - getCoreBuildDuration()
     * - getSpecializationDuration()
     * - getMetrics().timeCount() / (1000 * 1000) (so in milliseconds)
     * - solutions.size()
     * - completed ? 1 : 0
     *
     * @return a CSV formatted line.
     */
    String toCSV();
}
