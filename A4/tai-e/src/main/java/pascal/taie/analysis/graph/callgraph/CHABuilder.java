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
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

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
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Queue<JMethod> wl = new ArrayDeque<>();
        wl.add(entry);
        while (!wl.isEmpty()) {
            JMethod m = wl.remove();
            if (!callGraph.contains(m)) {
                callGraph.addReachableMethod(m);
                m.getIR().forEach(stmt -> {
                    if (stmt instanceof Invoke) {
                        Invoke cs = (Invoke) stmt;
                        Set<JMethod> T = resolve(cs);
                        T.forEach(mm -> {
                            callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(cs), cs, mm));
                            wl.add(mm);
                        });
                    }
                });
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> T = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        CallKind kind =  CallGraphs.getCallKind(callSite);
        if (kind == CallKind.STATIC) {
            T.add(methodRef.getDeclaringClass().getDeclaredMethod(methodRef.getSubsignature()));
        } else if (kind == CallKind.SPECIAL) {
            JMethod m = dispatch(methodRef.getDeclaringClass(), methodRef.getSubsignature());
            if (m != null) {
                T.add(m);
            }
        } else if (kind == CallKind.VIRTUAL || kind == CallKind.INTERFACE) {
            JClass c = methodRef.getDeclaringClass();
            Subsignature s = methodRef.getSubsignature();
            Queue<JClass> q = new ArrayDeque<>();
            q.add(c);
            while (!q.isEmpty()) {
                JClass cc = q.remove();
                JMethod m = dispatch(cc, s);
                if (m != null) {
                    T.add(m);
                }
                if (cc.isInterface()) {
                    q.addAll(hierarchy.getDirectSubinterfacesOf(cc));
                    q.addAll(hierarchy.getDirectImplementorsOf(cc));
                } else {
                    q.addAll(hierarchy.getDirectSubclassesOf(cc));
                }
            }
        }
        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        if (jclass == null) {
            return null;
        }
        JMethod m = jclass.getDeclaredMethod(subsignature);
        if (m != null) {
            if (!m.isAbstract()) {
                return m;
            }
        }
        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
