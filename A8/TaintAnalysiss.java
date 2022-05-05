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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Sets;

import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        result.getCSCallGraph().edges().forEach(edge -> {
            CSCallSite csCallSite = edge.getCallSite();
            JMethod method = edge.getCallee().getMethod();
            Invoke l = csCallSite.getCallSite();
            Context c = csCallSite.getContext();
            for (int i = 0; i < method.getParamCount(); ++i) {
                CSVar a = csManager.getCSVar(c, l.getInvokeExp().getArg(i));
                if (config.getSinks().contains(new Sink(method, i))) {
                    PointsToSet pa = a.getPointsToSet();
                    for (CSObj csObj : pa) {
                        Obj obj = csObj.getObject();
                        if (manager.isTaint(obj)) {
                            taintFlows.add(new TaintFlow(manager.getSourceCall(obj), l, i));
                        }
                    }
                }
            }
        });
        return taintFlows;
    }

    public Set<Type> getSources(JMethod method) {
        Set<Type> result = Sets.newHybridSet();
        config.getSources().forEach(source -> {
            if (source.method() == method) {
                result.add(source.type());
            }
        });
        return result;
    }

    public CSObj getTaintObj(Invoke source, Type type) {
        return csManager.getCSObj(emptyContext, manager.makeTaint(source, type));
    }

    private Set<Type> getTaintTransfers(JMethod method, int from, int to) {
        Set<Type> result = Sets.newHybridSet();
        config.getTransfers().forEach(transfer -> {
            if (transfer.method().equals(method) && transfer.from() == from && transfer.to() == to) {
                result.add(transfer.type());
            }
        });
        return result;
    }

    public Set<Type> getBaseToResultTransfers(JMethod method) {
        return getTaintTransfers(method, TaintTransfer.BASE, TaintTransfer.RESULT);
    }

    public Set<Type> getArgToBaseTransfers(JMethod method, int index) {
        return getTaintTransfers(method, index, TaintTransfer.BASE);
    }

    public Set<Type> getArgToResultTransfers(JMethod method, int index) {
        return getTaintTransfers(method, index, TaintTransfer.RESULT);
    }

    public boolean isTaint(CSObj csObj) {
        return manager.isTaint(csObj.getObject());
    }

    public Invoke getSourceCall(CSObj csObj) {
        return manager.getSourceCall(csObj.getObject());
    }

}
