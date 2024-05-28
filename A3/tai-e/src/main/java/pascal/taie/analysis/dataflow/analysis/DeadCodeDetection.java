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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;

import java.util.Comparator;
import java.util.Queue;
import java.util.Set;
import java.util.TreeSet;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        ir.stmts().forEach(deadCode::add);

        Queue<Stmt> workList = new java.util.LinkedList<>();
        Set<Stmt> visited = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        workList.add(cfg.getEntry());
        Stmt p;
        while ((p = workList.poll()) != null) {
            deadCode.remove(p);
            if (!visited.add(p)) continue;
            if (p instanceof Return) {
            } else if (p instanceof If i) {
                Value v = ConstantPropagation.evaluate(i.getCondition(), constants.getInFact(p));
                if (v.isNAC()) {
                    workList.addAll(cfg.getSuccsOf(p));
                    continue;
                }
                assert v.isConstant();
                int cs = v.getConstant();
                cfg.getOutEdgesOf(p).forEach(e -> {
                    if (e.getKind() == Edge.Kind.IF_TRUE && cs != 0) workList.add(e.getTarget());
                    if (e.getKind() == Edge.Kind.IF_FALSE && cs == 0) workList.add(e.getTarget());
                });
            } else if (p instanceof SwitchStmt c) {
                Value v = ConstantPropagation.evaluate(c.getVar(), constants.getInFact(p));
                if (v.isNAC()) {
                    workList.addAll(cfg.getSuccsOf(p));
                    continue;
                }
                assert v.isConstant();
                int cv = v.getConstant();
                boolean found = false;
                for (Edge<Stmt> e : cfg.getOutEdgesOf(p)) {
                    if (e.getKind() == Edge.Kind.SWITCH_CASE
                            && e.getCaseValue() == cv
                    ) {
                        workList.add(e.getTarget());
                        found = true;
                    }
                }
                if (!found) {
                    cfg.getOutEdgesOf(p).stream()
                            .filter(e -> e.getKind() == Edge.Kind.SWITCH_DEFAULT)
                            .findFirst().ifPresent(e -> workList.add(e.getTarget()));
                }
            } else if (p instanceof AssignStmt<?, ?> a) {
                RValue r = a.getRValue();
                LValue l = a.getLValue();
                if (l instanceof Var lv)
                    if (hasNoSideEffect(r) && !liveVars.getOutFact(p).contains(lv)) {
                        deadCode.add(p);
                    }
                workList.addAll(cfg.getSuccsOf(p));
            } else {
                workList.addAll(cfg.getSuccsOf(p));
                System.err.println("Unknown statement type: " + p.getClass() + " " + p);
            }
        }
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
