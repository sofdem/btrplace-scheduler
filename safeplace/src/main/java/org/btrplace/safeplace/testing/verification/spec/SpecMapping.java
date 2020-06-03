/*
 * Copyright  2020 The BtrPlace Authors. All rights reserved.
 * Use of this source code is governed by a LGPL-style
 * license that can be found in the LICENSE.txt file.
 */

package org.btrplace.safeplace.testing.verification.spec;

import org.btrplace.model.Mapping;
import org.btrplace.model.Node;
import org.btrplace.model.VM;
import org.btrplace.safeplace.spec.type.NodeStateType;
import org.btrplace.safeplace.spec.type.VMStateType;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * @author Fabien Hermenier
 */
public class SpecMapping {

  private final Map<VM, VMStateType.Type> vmState;

  private final Map<Node, NodeStateType.Type> nodeState;

  private final Map<VM, Node> activeOn;

  private final Map<Node, Set<VM>> host;

    public SpecMapping(Mapping ma) {
        vmState = new HashMap<>(ma.getNbVMs());
        activeOn = new HashMap<>(ma.getNbVMs());
        nodeState = new HashMap<>(ma.getNbNodes());
        host = new HashMap<>();
        for (Node n : ma.getOnlineNodes()) {
            nodeState.put(n, NodeStateType.Type.ONLINE);
            host.put(n, new HashSet<>());
            for (VM v : ma.getRunningVMs(n)) {
                vmState.put(v, VMStateType.Type.RUNNING);
                activeOn.put(v, n);
                host.get(n).add(v);
            }
            for (VM v : ma.getSleepingVMs(n)) {
                vmState.put(v, VMStateType.Type.SLEEPING);
                activeOn.put(v, n);
                host.get(n).add(v);
            }
        }
        for (Node n : ma.getOfflineNodes()) {
            nodeState.put(n, NodeStateType.Type.OFFLINE);
            host.put(n, new HashSet<>());
        }
        for (VM v : ma.getReadyVMs()) {
            vmState.put(v, VMStateType.Type.READY);
        }
    }

    public VMStateType.Type state(VM vm) {
        return vmState.get(vm);
    }

    public NodeStateType.Type state(Node n) {
        return nodeState.get(n);
    }

    public void state(Node n, NodeStateType.Type t) {
        nodeState.put(n, t);
    }

    public void state(VM v, VMStateType.Type t) {
        vmState.put(v, t);
    }

    public Set<VM> vms() {
        return vmState.keySet();
    }

    public Set<Node> nodes() {
        return nodeState.keySet();
    }

    public Node host(VM v) {
        return activeOn.get(v);
    }

    public void unhost(Node n, VM v) {
        host.get(n).remove(v);
    }

    public void host(VM v, Node n) {
        host.get(n).add(v);
    }

    public void activateOn(VM v, Node n) {
        host(v, n);
        activeOn.put(v, n);
    }

    public void desactivate(VM v) {
        activeOn.remove(v);
    }

    public Set<VM> runnings(Node n) {
        return host.get(n).stream()
                .filter(v -> state(v).equals(VMStateType.Type.RUNNING))
                .collect(Collectors.toSet());
    }

    public Set<VM> sleeping(Node n) {
        return host.get(n).stream()
                .filter(v -> state(v).equals(VMStateType.Type.SLEEPING))
                .collect(Collectors.toSet());
    }

    public Set<VM> ready() {
        return vmState.entrySet().stream()
                .filter(e -> e.getValue() == VMStateType.Type.READY)
                .map(Map.Entry::getKey)
                .collect(Collectors.toSet());
    }

    public Set<VM> hosted(Node n) {
        return host.get(n);

    }

    @Override
    public String toString() {
        return "SpecMapping{" +
                "vmState=" + vmState +
                ", nodeState=" + nodeState +
                ", activeOn=" + activeOn +
                ", host=" + host +
                '}';
    }
}
