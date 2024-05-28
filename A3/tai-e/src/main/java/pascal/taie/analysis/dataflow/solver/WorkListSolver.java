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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.analysis.LiveVariableAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        if (analysis instanceof ConstantPropagation){
            boolean changed = true;
            while (changed){
                changed = false;
                for (Node n : cfg){
                    Fact inFact;
                    if (!n.equals(cfg.getEntry())) {
                        inFact = analysis.newInitialFact();
                        for (Node p : cfg.getPredsOf(n)) {
                            analysis.meetInto(result.getOutFact(p), inFact);
                        }
                        result.setInFact(n, inFact);
                    } else {
                        inFact = result.getInFact(n);
                    }
                    if (result.getOutFact(n) == null){
                        Fact outFact = analysis.newInitialFact();
                        analysis.meetInto(inFact, outFact);
                        result.setOutFact(n, outFact);
                    }
                    changed |= analysis.transferNode(n, inFact, result.getOutFact(n));
                }
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        if (analysis instanceof LiveVariableAnalysis) {
            boolean changed = true;
            Node exit = cfg.getExit();
            while (changed) {
                changed = false;
                for (Node node : cfg) {
                    if (node.equals(exit)) continue;
                    Fact outFact = result.getOutFact(node);
                    if (outFact == null) {
                        outFact = analysis.newInitialFact();
                    }
                    for (Node s : cfg.getSuccsOf(node)) {
                        analysis.meetInto(result.getInFact(s), outFact);
                    }
                    result.setOutFact(node, outFact);
                    changed |= analysis.transferNode(node, result.getInFact(node), outFact);
                }
            }
        }
    }
}
