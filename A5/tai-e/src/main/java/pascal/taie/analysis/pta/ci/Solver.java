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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (callGraph.contains(method)) return;
        callGraph.addReachableMethod(method);
        method.getIR().stmts().forEach(stmt -> stmt.accept(stmtProcessor));
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            System.err.println("Visit: " + stmt);
            Var target = stmt.getLValue();
            Obj source = heapModel.getObj(stmt);
            PointsToSet pts = new PointsToSet(source);
            workList.addEntry(pointerFlowGraph.getVarPtr(target), pts);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            System.err.println("Visit: " + stmt);
            addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getVarPtr(stmt.getLValue()));
            return null;
        }

        @Override
        public Void visitDefault(Stmt stmt) {
            System.err.println("Visit: " + stmt);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            System.err.println("Visit: " + stmt);
            Var target = stmt.getLValue();
            JField source = stmt.getRValue().getFieldRef().resolve();
            if (!source.isStatic()) return null;
            addPFGEdge(pointerFlowGraph.getStaticField(source), pointerFlowGraph.getVarPtr(target));
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            System.err.println("Visit: " + stmt);
            JField target = stmt.getLValue().getFieldRef().resolve();
            Var source = stmt.getRValue();
            if (!stmt.isStatic()) return null;
            addPFGEdge(pointerFlowGraph.getVarPtr(source), pointerFlowGraph.getStaticField(target));
            return null;
        }

        @Override
        public Void visit(Invoke iv) {
            System.err.println("Visit: " + iv);
            if (!iv.isStatic()) return null;

            InvokeStatic ive = (InvokeStatic) iv.getInvokeExp();
            JMethod resolved = ive.getMethodRef().resolve();

            callGraph.addEdge(new Edge<>(resolveCallKind(iv), iv, resolved));
            addReachable(resolved);

            List<Var> args = ive.getArgs();
            List<Var> params = resolved.getIR().getParams();
            // param[i] = arg[i]
            // arg[i] -> param[i]
            for (int i = 0; i < args.size(); i++) {
                addPFGEdge(pointerFlowGraph.getVarPtr(args.get(i)), pointerFlowGraph.getVarPtr(params.get(i)));
            }

            Var save = iv.getLValue();
            if (save == null) return null;
            List<Var> ret = resolved.getIR().getReturnVars();
            ret.forEach(r -> addPFGEdge(pointerFlowGraph.getVarPtr(r), pointerFlowGraph.getVarPtr(save)));
            return null;

        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        System.err.println("Add edge: " + source + " -> " + target);
        if (pointerFlowGraph.getSuccsOf(source).contains(target)) return;
        pointerFlowGraph.addEdge(source, target);
        if (source.getPointsToSet().isEmpty()) return;
        workList.addEntry(target, source.getPointsToSet());
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // PointsToSet 指针指过的对象的集合
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer(); // 指针
            System.err.println("Processing: " + pointer);
            PointsToSet pointsToSet = entry.pointsToSet(); // 新的对象集合
            PointsToSet delta = propagate(pointer, pointsToSet);
            if (delta.isEmpty()) continue;
            // 如果有新的对象要指

            pointerFlowGraph.getSuccsOf(pointer).forEach(succ -> {
                // pointer指向的对象发生变化
                // 尝试让指向曾经指向pointer的指针指向新的对象
                workList.addEntry(succ, delta);
            });
            if (!(pointer instanceof VarPtr)) continue;

            Var v = ((VarPtr) pointer).getVar();
            for (Obj o : delta) {
                // v->f = r_var
                v.getStoreFields().forEach(s -> {
                    // get o.f
                    InstanceField of = pointerFlowGraph.getInstanceField(o, s.getFieldRef().resolve());
                    addPFGEdge(pointerFlowGraph.getVarPtr(s.getRValue()), of);
                });

                // l_var = v->f
                v.getLoadFields().forEach(l -> {
                    // get o.f
                    InstanceField of = pointerFlowGraph.getInstanceField(o, l.getFieldRef().resolve());
                    addPFGEdge(of, pointerFlowGraph.getVarPtr(l.getLValue()));
                });

                // l_var = v[*]
                v.getLoadArrays().forEach(l -> {
                    VarPtr target = pointerFlowGraph.getVarPtr(l.getLValue());
                    addPFGEdge(pointerFlowGraph.getArrayIndex(o), target);
                });

                // v[*] = r_var
                v.getStoreArrays().forEach(s -> {
                    VarPtr source = pointerFlowGraph.getVarPtr(s.getRValue());
                    addPFGEdge(source, pointerFlowGraph.getArrayIndex(o));
                });

                // 在v指向o的情况下，更新调用图
                processCall(v, o);
            }

        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet old = pointer.getPointsToSet();
        PointsToSet diff = new PointsToSet();
        for (Obj o : pointsToSet) {
            if (!old.contains(o)) {
                diff.addObject(o);
                old.addObject(o);
            }
        }
        return diff;
    }

    private CallKind resolveCallKind(Invoke cs) {
        if (cs.isStatic()) return CallKind.STATIC;
        if (cs.isVirtual()) return CallKind.VIRTUAL;
        if (cs.isSpecial()) return CallKind.SPECIAL;
        if (cs.isInterface()) return CallKind.INTERFACE;
        if (cs.isDynamic()) return CallKind.DYNAMIC;
        return CallKind.OTHER;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        var.getInvokes().forEach(callSite -> {
            JMethod callee = resolveCallee(recv, callSite);
            // 尝试让this指向新的对象
            workList.addEntry(pointerFlowGraph.getVarPtr(callee.getIR().getThis()), new PointsToSet(recv));

            if (!callGraph.addEdge(new Edge<>(resolveCallKind(callSite), callSite, callee))) return;
            addReachable(callee);

            List<Var> args = callSite.getInvokeExp().getArgs();
            List<Var> params = callee.getIR().getParams();
            // param[i] = arg[i]
            // arg[i] -> param[i]
            for (int i = 0; i < args.size(); i++) {
                addPFGEdge(pointerFlowGraph.getVarPtr(args.get(i)), pointerFlowGraph.getVarPtr(params.get(i)));
            }

            Var save = callSite.getLValue();
            if (save == null) return;
            List<Var> ret = callee.getIR().getReturnVars();
            ret.forEach(r -> addPFGEdge(pointerFlowGraph.getVarPtr(r), pointerFlowGraph.getVarPtr(save)));
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
