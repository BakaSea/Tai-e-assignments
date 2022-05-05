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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.MapFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private MapFact<JField, Set<StoreField>> staticStoreFields;

    private MapFact<JField, Set<LoadField>> staticLoadFields;

    private MapFact<Var, Set<StoreField>> instanceStoreFields;

    private MapFact<Var, Set<LoadField>> instanceLoadFields;

    private MapFact<Var, Set<StoreArray>> storeArrays;

    private MapFact<Var, Set<LoadArray>> loadArrays;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here
        staticStoreFields = new MapFact<>(Collections.emptyMap());
        staticLoadFields = new MapFact<>(Collections.emptyMap());
        instanceStoreFields = new MapFact<>(Collections.emptyMap());
        instanceLoadFields = new MapFact<>(Collections.emptyMap());
        storeArrays = new MapFact<>(Collections.emptyMap());
        loadArrays = new MapFact<>(Collections.emptyMap());
        pta.getVars().forEach(target -> {
            instanceStoreFields.update(target, new HashSet<>(target.getStoreFields()));
            instanceLoadFields.update(target, new HashSet<>(target.getLoadFields()));
            storeArrays.update(target, new HashSet<>(target.getStoreArrays()));
            loadArrays.update(target, new HashSet<>(target.getLoadArrays()));
            pta.getVars().forEach(source -> {
                if (source != target) {
                    Set<Obj> overlap = new HashSet<>(pta.getPointsToSet(source));
                    overlap.retainAll(pta.getPointsToSet(target));
                    if (!overlap.isEmpty()) {
                        instanceStoreFields.get(target).addAll(source.getStoreFields());
                        instanceLoadFields.get(target).addAll(source.getLoadFields());
                        storeArrays.get(target).addAll(source.getStoreArrays());
                        loadArrays.get(target).addAll(source.getLoadArrays());
                    }
                }
            });
        });
        pta.getCallGraph().reachableMethods().forEach(method -> method.getIR().forEach(stmt -> {
            if (stmt instanceof StoreField) {
                StoreField storeField = (StoreField) stmt;
                if (storeField.isStatic()) {
                    JField field = storeField.getFieldRef().resolve();
                    Set<StoreField> storeFields = staticStoreFields.get(field);
                    if (storeFields == null) {
                        storeFields = new HashSet<>();
                        staticStoreFields.update(field, storeFields);
                    }
                    storeFields.add(storeField);
                }
            } else if (stmt instanceof LoadField) {
                LoadField loadField = (LoadField) stmt;
                if (loadField.isStatic()) {
                    JField field = loadField.getFieldRef().resolve();
                    Set<LoadField> loadFields = staticLoadFields.get(field);
                    if (loadFields == null) {
                        loadFields = new HashSet<>();
                        staticLoadFields.update(field, loadFields);
                    }
                    loadFields.add(loadField);
                }
            }
        }));
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt instanceof DefinitionStmt) {
            LValue l = ((DefinitionStmt<?, ?>) stmt).getLValue();
            if (l != null) {
                if (l instanceof Var) {
                    Var var = (Var) l;
                    if (ConstantPropagation.canHoldInt(var)) {
                        out.remove(var);
                        if (stmt instanceof LoadField) {
                            CPFact oldOut = out.copy();
                            out.copyFrom(in);
                            LoadField loadField = (LoadField) stmt;
                            if (loadField.isStatic()) {
                                Value value = Value.getUndef();
                                Set<StoreField> storeFields = staticStoreFields.get(loadField.getFieldRef().resolve());
                                if (storeFields != null) {
                                    for (StoreField storeField : storeFields) {
                                        CPFact fact = solver.getOutFact(storeField);
                                        if (fact != null) {
                                            value = cp.meetValue(value, fact.get(storeField.getRValue()));
                                        }
                                    }
                                }
                                out.update(var, value);
                                return !oldOut.equals(out);
                            } else {
                                InstanceFieldAccess fieldAccess = (InstanceFieldAccess) loadField.getFieldAccess();
                                Set<StoreField> storeFields = instanceStoreFields.get(fieldAccess.getBase());
                                Value value = Value.getUndef();
                                if (storeFields != null) {
                                    for (StoreField storeField : storeFields) {
                                        if (storeField.getFieldRef().resolve() == loadField.getFieldRef().resolve()) {
                                            CPFact fact = solver.getOutFact(storeField);
                                            if (fact != null) {
                                                value = cp.meetValue(value, fact.get(storeField.getRValue()));
                                            }
                                        }
                                    }
                                }
                                out.update(var, value);
                                return !oldOut.equals(out);
                            }
                        } else if (stmt instanceof LoadArray) {
                            CPFact oldOut = out.copy();
                            out.copyFrom(in);
                            LoadArray loadArray = (LoadArray) stmt;
                            ArrayAccess loadArrayAccess = loadArray.getArrayAccess();
                            Set<StoreArray> storeArraySet = storeArrays.get(loadArrayAccess.getBase());
                            Value c1 = in.get(loadArrayAccess.getIndex());
                            Value value = Value.getUndef();
                            if (storeArraySet != null) {
                                for (StoreArray storeArray : storeArraySet) {
                                    CPFact fact = solver.getOutFact(storeArray);
                                    if (fact != null) {
                                        Value c2 = fact.get(storeArray.getArrayAccess().getIndex());
                                        if ((c1.isNAC() && c2.isNAC())
                                                || (c1.isNAC() && c2.isConstant())
                                                || (c1.isConstant() && c2.isNAC())
                                                || (c1.isConstant() && c2.isConstant() && c1.getConstant() == c2.getConstant())) {
                                            value = cp.meetValue(value, fact.get(storeArray.getRValue()));
                                        }
                                    }
                                }
                            }
                            out.update(var, value);
                            return !oldOut.equals(out);
                        }
                    }
                }
            }
        }
        boolean flag = cp.transferNode(stmt, in, out);
        if (flag) {
            if (stmt instanceof StoreField) {
                StoreField storeField = (StoreField) stmt;
                if (storeField.isStatic()) {
                    Set<LoadField> loadFields = staticLoadFields.get(storeField.getFieldRef().resolve());
                    if (loadFields != null) {
                        for (LoadField loadField : loadFields) {
                            if (loadField.getFieldRef().resolve() == storeField.getFieldRef().resolve()) {
                                solver.addWorklistEntry(loadField);
                            }
                        }
                    }
                } else {
                    InstanceFieldAccess fieldAccess = (InstanceFieldAccess) storeField.getFieldAccess();
                    Set<LoadField> loadFields = instanceLoadFields.get(fieldAccess.getBase());
                    if (loadFields != null) {
                        for (LoadField loadField : loadFields) {
                            if (loadField.getFieldRef().resolve() == storeField.getFieldRef().resolve()) {
                                solver.addWorklistEntry(loadField);
                            }
                        }
                    }
                }
            } else if (stmt instanceof StoreArray) {
                Set<LoadArray> loadArraySet = loadArrays.get(((StoreArray) stmt).getArrayAccess().getBase());
                if (loadArraySet != null) {
                    loadArraySet.forEach(solver::addWorklistEntry);
                }
            }
        }
        return flag;
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact edgeOut = out.copy();
        Stmt source = edge.getSource();
        if (source instanceof Invoke) {
            Var result = ((Invoke) source).getResult();
            if (result != null) {
                edgeOut.remove(result);
            }
        }
        return edgeOut;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        CPFact out = new CPFact();
        Stmt source = edge.getSource();
        if (source instanceof Invoke) {
            InvokeExp exp = ((Invoke) source).getInvokeExp();
            JMethod m = edge.getCallee();
            for (int i = 0; i < m.getParamCount(); ++i) {
                out.update(m.getIR().getParam(i), callSiteOut.get(exp.getArg(i)));
            }
        }
        return out;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact out = new CPFact();
        Stmt callSite = edge.getCallSite();
        if (callSite instanceof Invoke) {
            Var result = ((Invoke) callSite).getResult();
            if (result != null) {
                List<Var> returnVars = edge.getReturnVars().stream().collect(Collectors.toList());
                Value val = Value.getUndef();
                for (Var var : returnVars) {
                    val = cp.meetValue(val, returnOut.get(var));
                }
                out.update(result, val);
            }
        }
        return out;
    }
}
