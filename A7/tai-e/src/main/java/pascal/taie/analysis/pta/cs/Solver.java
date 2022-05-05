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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if (callGraph.addReachableMethod(csMethod)) {
            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
            csMethod.getMethod().getIR().forEach(stmt -> stmt.accept(stmtProcessor));
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            Obj obj = heapModel.getObj(stmt);
            workList.addEntry(csManager.getCSVar(context, stmt.getLValue()), PointsToSetFactory.make(csManager.getCSObj(contextSelector.selectHeapContext(csMethod, obj), obj)));
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(csManager.getCSVar(context, stmt.getRValue()), csManager.getCSVar(context, stmt.getLValue()));
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod m = resolveCallee(null, stmt);
                Context ct = contextSelector.selectContext(csManager.getCSCallSite(context, stmt), m);
                if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt), csManager.getCSCallSite(context, stmt), csManager.getCSMethod(ct, m)))) {
                    addReachable(csManager.getCSMethod(ct, m));
                    for (int i = 0; i < m.getParamCount(); ++i) {
                        Var a = stmt.getInvokeExp().getArg(i);
                        Var p = m.getIR().getParam(i);
                        addPFGEdge(csManager.getCSVar(context, a), csManager.getCSVar(ct, p));
                    }
                    if (stmt.getResult() != null) {
                        for (Var ret : m.getIR().getReturnVars()) {
                            addPFGEdge(csManager.getCSVar(ct, ret), csManager.getCSVar(context, stmt.getResult()));
                        }
                    }
                }
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(csManager.getCSVar(context, stmt.getRValue()), csManager.getStaticField(stmt.getFieldRef().resolve()));
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(csManager.getStaticField(stmt.getFieldRef().resolve()), csManager.getCSVar(context, stmt.getLValue()));
            }
            return StmtVisitor.super.visit(stmt);
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet delta = propagate(entry.pointer(), entry.pointsToSet());
            if (entry.pointer() instanceof CSVar) {
                CSVar csVar = (CSVar) entry.pointer();
                Context c = csVar.getContext();
                Var var = csVar.getVar();
                for (CSObj csObj : delta) {
                    for (StoreField stmt : var.getStoreFields()) {
                        if (stmt.isStatic()) {
                            addPFGEdge(csManager.getCSVar(c, stmt.getRValue()), csManager.getStaticField(stmt.getFieldRef().resolve()));
                        } else {
                            addPFGEdge(csManager.getCSVar(c, stmt.getRValue()), csManager.getInstanceField(csObj, stmt.getFieldRef().resolve()));
                        }
                    }
                    for (LoadField stmt : var.getLoadFields()) {
                        if (stmt.isStatic()) {
                            addPFGEdge(csManager.getStaticField(stmt.getFieldRef().resolve()), csManager.getCSVar(c, stmt.getLValue()));
                        } else {
                            addPFGEdge(csManager.getInstanceField(csObj, stmt.getFieldRef().resolve()), csManager.getCSVar(c, stmt.getLValue()));
                        }
                    }
                    for (StoreArray stmt : var.getStoreArrays()) {
                        addPFGEdge(csManager.getCSVar(c, stmt.getRValue()), csManager.getArrayIndex(csObj));
                    }
                    for (LoadArray stmt : var.getLoadArrays()) {
                        addPFGEdge(csManager.getArrayIndex(csObj), csManager.getCSVar(c, stmt.getLValue()));
                    }
                    processCall(csVar, csObj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet delta = PointsToSetFactory.make();
        if (!pointsToSet.isEmpty()) {
            for (CSObj csObj : pointsToSet) {
                if (pointer.getPointsToSet().addObject(csObj)) {
                    delta.addObject(csObj);
                }
            }
            if (!delta.isEmpty()) {
                pointerFlowGraph.getSuccsOf(pointer).forEach(succ -> workList.addEntry(succ, delta));
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        Context c = recv.getContext();
        for (Invoke stmt : recv.getVar().getInvokes()) {
            JMethod m = resolveCallee(recvObj, stmt);
            Context ct = contextSelector.selectContext(csManager.getCSCallSite(c, stmt), recvObj, m);
            workList.addEntry(csManager.getCSVar(ct, m.getIR().getThis()), PointsToSetFactory.make(recvObj));
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt), csManager.getCSCallSite(c, stmt), csManager.getCSMethod(ct, m)))) {
                addReachable(csManager.getCSMethod(ct, m));
                for (int i = 0; i < m.getParamCount(); ++i) {
                    Var a = stmt.getInvokeExp().getArg(i);
                    Var p = m.getIR().getParam(i);
                    addPFGEdge(csManager.getCSVar(c, a), csManager.getCSVar(ct, p));
                }
                if (stmt.getResult() != null) {
                    for (Var ret : m.getIR().getReturnVars()) {
                        addPFGEdge(csManager.getCSVar(ct, ret), csManager.getCSVar(c, stmt.getResult()));
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
