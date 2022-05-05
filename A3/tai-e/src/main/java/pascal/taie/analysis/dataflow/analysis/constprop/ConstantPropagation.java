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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact result = new CPFact();
        for (Var v : cfg.getIR().getParams()) {
            if (canHoldInt(v)) {
                result.update(v, Value.getNAC());
            }
        }
        return result;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.forEach((key, value) -> target.update(key, meetValue(value, target.get(key))));
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC() || v2.isNAC()) return Value.getNAC();
        if (v1.isUndef()) return v2;
        if (v2.isUndef()) return v1;
        if (v1.getConstant() == v2.getConstant()) return v1;
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact oldOut = out.copy();
        out.copyFrom(in);
        if (stmt instanceof DefinitionStmt) {
            DefinitionStmt<?, ?> def = (DefinitionStmt<?, ?>)stmt;
            LValue l = def.getLValue();
            RValue r = def.getRValue();
            if (l != null) {
                if (l instanceof Var) {
                    Var lv = (Var)l;
                    if (canHoldInt(lv)) {
                        out.remove(lv);
                        out.update(lv, evaluate(r, in));
                    }
                }
            }
        }
        for (Var v : oldOut.keySet()) {
            if (oldOut.get(v) != Value.getUndef()) {
                if (!out.get(v).equals(oldOut.get(v))) {
                    return true;
                }
            }
        }
        for (Var v : out.keySet()) {
            if (out.get(v) != Value.getUndef()) {
                if (!oldOut.get(v).equals(out.get(v))) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        } else if (exp instanceof Var) {
            Value value = in.get((Var)exp);
            if (value != null) {
                return value;
            } else {
                return Value.getUndef();
            }
        } else if (exp instanceof BinaryExp) {
            Value v1 = in.get(((BinaryExp) exp).getOperand1());
            Value v2 = in.get(((BinaryExp) exp).getOperand2());
            if (exp instanceof ArithmeticExp) {
                if (((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.DIV || ((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.REM) {
                    if (v2.isConstant()) {
                        if (v2.getConstant() == 0) {
                            return Value.getUndef();
                        }
                    }
                }
            }
            if (v1.isConstant() && v2.isConstant()) {
                if (exp instanceof ArithmeticExp) {
                    switch (((ArithmeticExp) exp).getOperator()) {
                        case ADD: return Value.makeConstant(v1.getConstant()+v2.getConstant());
                        case SUB: return Value.makeConstant(v1.getConstant()-v2.getConstant());
                        case MUL: return Value.makeConstant(v1.getConstant()*v2.getConstant());
                        case DIV:
                            if (v2.getConstant() == 0) return Value.getUndef();
                            else return Value.makeConstant(v1.getConstant()/v2.getConstant());
                        case REM:
                            if (v2.getConstant() == 0) return Value.getUndef();
                            else return Value.makeConstant(v1.getConstant()%v2.getConstant());
                    }
                } else if (exp instanceof ConditionExp) {
                    switch (((ConditionExp) exp).getOperator()) {
                        case EQ:
                            if (v1.getConstant() == v2.getConstant()) return Value.makeConstant(1);
                            else return Value.makeConstant(0);
                        case NE:
                            if (v1.getConstant() != v2.getConstant()) return Value.makeConstant(1);
                            else return Value.makeConstant(0);
                        case LT:
                            if (v1.getConstant() < v2.getConstant()) return Value.makeConstant(1);
                            else return Value.makeConstant(0);
                        case GT:
                            if (v1.getConstant() > v2.getConstant()) return Value.makeConstant(1);
                            else return Value.makeConstant(0);
                        case LE:
                            if (v1.getConstant() <= v2.getConstant()) return Value.makeConstant(1);
                            else return Value.makeConstant(0);
                        case GE:
                            if (v1.getConstant() >= v2.getConstant()) return Value.makeConstant(1);
                            else return Value.makeConstant(0);
                    }
                } else if (exp instanceof ShiftExp) {
                    switch (((ShiftExp) exp).getOperator()) {
                        case SHL: return Value.makeConstant(v1.getConstant() << v2.getConstant());
                        case SHR: return Value.makeConstant(v1.getConstant() >> v2.getConstant());
                        case USHR: return Value.makeConstant(v1.getConstant() >>> v2.getConstant());
                    }
                } else if (exp instanceof BitwiseExp) {
                    switch (((BitwiseExp) exp).getOperator()) {
                        case OR: return Value.makeConstant(v1.getConstant() | v2.getConstant());
                        case AND: return Value.makeConstant(v1.getConstant() & v2.getConstant());
                        case XOR: return Value.makeConstant(v1.getConstant() ^ v2.getConstant());
                    }
                }
            } else if (v1.isNAC() || v2.isNAC()) {
                return Value.getNAC();
            } else {
                return Value.getUndef();
            }
        }
        return Value.getNAC();
    }
}
