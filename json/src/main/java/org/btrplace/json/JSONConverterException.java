/*
 * Copyright (c) 2016 University Nice Sophia Antipolis
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

package org.btrplace.json;

/**
 * An exception related to a conversion process.
 *
 * @author Fabien Hermenier
 */
public class JSONConverterException extends Exception {

    /**
     * Make a new exception.
     *
     * @param msg the error message
     */
    public JSONConverterException(String msg) {
        super(msg);
    }

    /**
     * Make a new exception.
     *
     * @param msg the error message
     * @param t   the root exception
     */
    public JSONConverterException(String msg, Throwable t) {
        super(msg, t);
    }

    /**
     * Rethrow an existing exception.
     *
     * @param t the exception to rethrow
     */
    public JSONConverterException(Throwable t) {
        super(t);
    }

    /**
     * State a node has already been declared.
     *
     * @param id the node identifier
     * @return the generated exception
     */
    public static JSONConverterException nodeAlreadyDeclared(int id) {
        return new JSONConverterException("Node '" + id + "' already declared");
    }

    /**
     * State a VM has already been declared.
     *
     * @param id the VM identifier
     * @return the generated exception
     */
    public static JSONConverterException vmAlreadyDeclared(int id) {
        return new JSONConverterException("VM '" + id + "' already declared");
    }

}
