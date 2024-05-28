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
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
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
        IR ir = cfg.getIR();
        CPFact fact = new CPFact();
        ir.getParams().forEach(k -> fact.update(k, Value.getNAC()));
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        if (fact == null) return;
        fact.forEach((k, v) -> {
            target.update(k, meetValue(target.get(k), v));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        assert v1 != null && v2 != null;
        if (v1.isNAC() || v2.isNAC()) return Value.getNAC();
        if (v1.isUndef()) return v2;
        if (v2.isUndef()) return v1;
        if (!v1.isConstant() || !v2.isConstant()) return Value.getNAC();
        if (v1.equals(v2)) return v1;
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        boolean changed = false;

        if (stmt instanceof AssignLiteral a) {
            IntLiteral r = (IntLiteral) a.getRValue();
            Value rv = Value.makeConstant(r.getValue());
            changed |= out.update(a.getLValue(), rv);
        } else if (stmt instanceof Copy c) {
            Var l = c.getLValue();
            Var r = c.getRValue();
            Value v = in.get(r);
            changed |= out.update(l, v);
        } else if (stmt instanceof Binary b) {
            BinaryExp r = b.getRValue();
            Value rv = evaluate(r, in);
            changed |= out.update(b.getLValue(), rv);
        } else if (stmt instanceof If i) {
        } else if (stmt instanceof Invoke n) {
        } else if (stmt instanceof Return r) {
        } else if (stmt instanceof Nop t) {
        } else if (stmt instanceof Goto g) {
        } else {
            System.err.println(stmt.getClass() + " " + stmt);
        }
        return changed;
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
        if (!(exp instanceof BinaryExp b)){
            if (exp instanceof Var v)
                return in.get(v);
            assert false : "Unsupported expression: " + exp;
        }
        BinaryExp b = (BinaryExp) exp;
        Var op1 = b.getOperand1();
        Var op2 = b.getOperand2();
        Value v1 = in.get(op1);
        Value v2 = in.get(op2);
        assert !v1.isUndef() && !v2.isUndef() : "Undefined value in evaluate";
        String op = b.getOperator().toString();
//        运算类型	运算符
//        Arithmetic	+ - * / %
//        Condition	== != < > <= >=
//        Shift	<< >> >>>
//        Bitwise	| & ^
        switch (op) {
            case "+":
                if (v1.isConstant() && v2.isConstant()) {
                    return Value.makeConstant(v1.getConstant() + v2.getConstant());
                }
                break;
            case "-":
                if (v1.isConstant() && v2.isConstant()) {
                    return Value.makeConstant(v1.getConstant() - v2.getConstant());
                }
                break;
            case "*":
                if (v1.isConstant() && v2.isConstant()) {
                    return Value.makeConstant(v1.getConstant() * v2.getConstant());
                }
                break;
            case "/":
                if (v1.isConstant() && v2.isConstant()) {
                    return Value.makeConstant(v1.getConstant() / v2.getConstant());
                }
                break;
            case "%":
                if (v1.isConstant() && v2.isConstant()) {
                    return Value.makeConstant(v1.getConstant() % v2.getConstant());
                }
                break;
            case "<<":
                if (v1.isConstant() && v2.isConstant()) {
                    return Value.makeConstant(v1.getConstant() << v2.getConstant());
                }
                break;
            case "|":
                if (v1.isConstant() && v2.isConstant()) {
                    return Value.makeConstant(v1.getConstant() | v2.getConstant());
                }
                break;
            case "&":
                if (v1.isConstant() && v2.isConstant()) {
                    return Value.makeConstant(v1.getConstant() & v2.getConstant());
                }
                break;
            case "==":
                if (v1.isConstant() && v2.isConstant()) {
                    return Value.makeConstant(v1.getConstant() == v2.getConstant() ? 1 : 0);
                }
                break;
            case "!=":
                if (v1.isConstant() && v2.isConstant()) {
                    return Value.makeConstant(v1.getConstant() != v2.getConstant() ? 1 : 0);
                }
                break;
            case "<":
                if (v1.isConstant() && v2.isConstant()) {
                    return Value.makeConstant(v1.getConstant() < v2.getConstant() ? 1 : 0);
                }
                break;
            case ">":
                if (v1.isConstant() && v2.isConstant()) {
                    return Value.makeConstant(v1.getConstant() > v2.getConstant() ? 1 : 0);
                }
                break;
            case "<=":
                if (v1.isConstant() && v2.isConstant()) {
                    return Value.makeConstant(v1.getConstant() <= v2.getConstant() ? 1 : 0);
                }
                break;
            case ">=":
                if (v1.isConstant() && v2.isConstant()) {
                    return Value.makeConstant(v1.getConstant() >= v2.getConstant() ? 1 : 0);
                }
                break;
            case ">>":
                if (v1.isConstant() && v2.isConstant()) {
                    return Value.makeConstant(v1.getConstant() >> v2.getConstant());
                }
                break;
            case ">>>":
                if (v1.isConstant() && v2.isConstant()) {
                    return Value.makeConstant(v1.getConstant() >>> v2.getConstant());
                }
                break;
            default:
                assert false : "Unsupported operator: " + op;
        }
        return Value.getNAC();
    }
}
