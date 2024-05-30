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

import com.sun.istack.NotNull;
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
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.*;
import java.util.stream.Stream;

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

    Solver(AnalysisOptions options, HeapModel heapModel, ContextSelector contextSelector) {
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
        if (callGraph.contains(csMethod)) return;
        callGraph.addReachableMethod(csMethod);
        JMethod method = csMethod.getMethod();
        StmtProcessor processor = new StmtProcessor(csMethod);
        method.getIR().stmts().forEach(s -> s.accept(processor));
    }

    private void addArgs(CSCallSite iv, CSMethod callee) {
        List<Var> source = iv.getCallSite().getInvokeExp().getArgs();
        List<Var> target = callee.getMethod().getIR().getParams();
        List<CSVar> sourceCSVars = new ArrayList<>();
        source.forEach(v -> sourceCSVars.add(csManager.getCSVar(iv.getContext(), v)));
        List<CSVar> targetCSVars = new ArrayList<>();
        target.forEach(v -> targetCSVars.add(csManager.getCSVar(callee.getContext(), v)));
        assert sourceCSVars.size() == targetCSVars.size();
        for (int i = 0; i < sourceCSVars.size(); i++) {
            addPFGEdge(sourceCSVars.get(i), targetCSVars.get(i));
        }
    }

    private void addRet(CSCallSite iv, CSMethod callee) {
        Var targetVar = iv.getCallSite().getLValue();
        if (targetVar == null) return;
        CSVar target = csManager.getCSVar(iv.getContext(), targetVar);
        JMethod resolved = callee.getMethod();
        List<Var> retVars = resolved.getIR().getReturnVars();
        List<CSVar> retCSVars = new ArrayList<>();
        retVars.forEach(v -> retCSVars.add(csManager.getCSVar(callee.getContext(), v)));
        retCSVars.forEach(v -> addPFGEdge(v, target));
    }

    private static CallKind resolveKind(Invoke stmt) {
        if (stmt.isDynamic()) return CallKind.DYNAMIC;
        if (stmt.isStatic()) return CallKind.STATIC;
        if (stmt.isSpecial()) return CallKind.SPECIAL;
        if (stmt.isVirtual()) return CallKind.VIRTUAL;
        if (stmt.isInterface()) return CallKind.INTERFACE;
        return CallKind.OTHER;
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
        public Void visitDefault(Stmt stmt) {
            System.err.printf("Visit(%s):%s\n", context, stmt);
            return null;
        }

        @Override
        public Void visit(New stmt) {
            visitDefault(stmt);
            Obj o = heapModel.getObj(stmt);
            CSObj cso = csManager.getCSObj(contextSelector.selectHeapContext(csMethod, o), o);
            PointsToSet pcso = PointsToSetFactory.make(cso);
            workList.addEntry(csManager.getCSVar(context, stmt.getLValue()), pcso);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            visitDefault(stmt);
            Var var = stmt.getRValue();
            Var suc = stmt.getLValue();
            addPFGEdge(csManager.getCSVar(context, var), csManager.getCSVar(context, suc));
            return null;
        }

        @Override
        public Void visit(LoadField stmt){
            // x = y.z
            visitDefault(stmt);
            if (!stmt.isStatic()) return null;
            FieldAccess fa = stmt.getFieldAccess();
            JField field = fa.getFieldRef().resolve();
            CSVar target = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(
                    csManager.getStaticField(field),
                    target
            );
            return null;
        }

        @Override
        public Void visit(StoreField stmt){
            // x.z = y
            visitDefault(stmt);
            if (!stmt.isStatic()) return null;
            FieldAccess fa = stmt.getFieldAccess();
            JField field = fa.getFieldRef().resolve();
            CSVar source = csManager.getCSVar(context, stmt.getRValue());
            addPFGEdge(
                    source,
                    csManager.getStaticField(field)
            );
            return null;
        }


        @Override
        public Void visit(Invoke stmt) {
            visitDefault(stmt);
            if (!stmt.isStatic()) return null;
            InvokeExp exp = stmt.getInvokeExp();
            CSCallSite cscs = csManager.getCSCallSite(context, stmt);
            JMethod callee = exp.getMethodRef().resolve();
            Context mCtx = contextSelector.selectContext(cscs, callee);
            System.err.println("NewContext: "+context+" -> "+ mCtx);
            CSMethod csm = csManager.getCSMethod(mCtx, callee);
            if (!callGraph.addEdge(new Edge<>(resolveKind(stmt), cscs, csm))) return null;
            addArgs(cscs, csm);
            addReachable(csm);
            addRet(cscs, csm);
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (!pointerFlowGraph.addEdge(source, target)) return;
        workList.addEntry(target, source.getPointsToSet());
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet delta = propagate(entry.pointer(), entry.pointsToSet());
            if (delta.isEmpty()) continue;
            pointerFlowGraph.getSuccsOf(entry.pointer()).forEach(p -> workList.addEntry(p, delta));
            if (entry.pointer() instanceof CSVar p) {
                Var var = p.getVar();
                Context ctx = p.getContext();
                delta.forEach(obj -> {
                    var.getStoreFields().forEach(stmt -> {
                        addPFGEdge(
                                csManager.getCSVar(ctx, stmt.getRValue()),
                                csManager.getInstanceField(obj, stmt.getFieldAccess().getFieldRef().resolve())
                        );
                    });
                    // LoadField
                    var.getLoadFields().forEach(stmt -> {
                        addPFGEdge(
                                csManager.getInstanceField(obj, stmt.getFieldAccess().getFieldRef().resolve()),
                                csManager.getCSVar(ctx, stmt.getLValue())
                        );
                    });
                    // StoreArray
                    var.getStoreArrays().forEach(stmt -> {
                        addPFGEdge(
                                csManager.getCSVar(ctx, stmt.getRValue()),
                                csManager.getArrayIndex(obj)
                        );
                    });
                    // LoadArray
                    var.getLoadArrays().forEach(stmt -> {
                        addPFGEdge(
                                csManager.getArrayIndex(obj),
                                csManager.getCSVar(ctx, stmt.getLValue())
                        );
                    });
                    processCall(p, obj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    @NotNull
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet oldObjs = pointer.getPointsToSet();
        PointsToSet diff = PointsToSetFactory.make();
        pointsToSet.objects().filter(o -> !oldObjs.contains(o)).forEach(csObj -> {
            oldObjs.addObject(csObj);
            diff.addObject(csObj);
        });
        return diff;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        recv.getVar().getInvokes().forEach(iv -> {
            JMethod callee = resolveCallee(recvObj, iv);
            Context callContext = recv.getContext();
            CSCallSite cscs = csManager.getCSCallSite(callContext, iv);
            Context calleeContext = contextSelector.selectContext(cscs, recvObj, callee);
            CSMethod csm = csManager.getCSMethod(calleeContext, callee);
            // !!!!!!!!重要
            // 用recvObj作为this，调用了方法，更新this的指向
            workList.addEntry(
                    csManager.getCSVar(calleeContext, callee.getIR().getThis()),
                    PointsToSetFactory.make(recvObj)
            );
            callGraph.addEdge(new Edge<>(resolveKind(iv), cscs, csm));
            addReachable(csm);
            addArgs(cscs, csm);
            addRet(cscs, csm);
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

