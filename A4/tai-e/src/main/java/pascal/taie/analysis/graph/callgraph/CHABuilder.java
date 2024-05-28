/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;
import polyglot.util.WorkList;

import java.lang.invoke.CallSite;
import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        Queue<JMethod> workList = new LinkedList<>();
        Set<JMethod> visited = new HashSet<>();
        workList.add(entry);
        callGraph.addEntryMethod(entry);
        callGraph.addReachableMethod(entry);
        while (!workList.isEmpty()) {
            JMethod method = workList.poll();
            if (!visited.add(method)) continue;
            for (Stmt s : method.getIR().getStmts()) {
                if (s instanceof Invoke inv) {
                    for (JMethod target : resolve(inv)) {
                        callGraph.addReachableMethod(target);
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(inv), inv, target));
                        workList.add(target);
                    }
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        MethodRef ref = callSite.getMethodRef();
        JClass jclass = ref.getDeclaringClass();
        Subsignature sig = ref.getSubsignature();
        TreeSet<JMethod> targets = new TreeSet<>(Comparator.comparing(JMethod::getSignature));
        Queue<JClass> workList;
        Set<JClass> visited;
        switch (CallGraphs.getCallKind(callSite)) {
            case VIRTUAL:
            case INTERFACE:
                workList = new LinkedList<>();
                visited = new HashSet<>();
                workList.add(jclass);
                while (!workList.isEmpty()) {
                    JClass c = workList.poll();
                    if (!visited.add(c)) continue;
                    if (c.isInterface()) {
                        workList.addAll(hierarchy.getDirectImplementorsOf(c));
                    } else if (c.isAbstract()) {
                        workList.addAll(hierarchy.getDirectSubclassesOf(c));
                    } else {
                        workList.addAll(hierarchy.getDirectSubclassesOf(c));
                        targets.add(dispatch(c, sig));
                    }
                }
                return targets;
            case SPECIAL:
            case STATIC:
                JMethod target = dispatch(jclass, sig);
                assert target != null : "unexpected null method";
                targets.add(target);
                return targets;
            default:
                System.err.println("unexpected call kind: " + CallGraphs.getCallKind(callSite));
                assert false : "unreachable";
        }
        return targets;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod m;
        if (jclass == null) return null;
        if ((m = jclass.getDeclaredMethod(subsignature)) != null) return m;
        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
