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
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.InvokeSpecial;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.*;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    public record CustomSink(Invoke invoke, int index) {
    }

    public Set<Pointer> getSuccsOf(Pointer var) {
        return pointerFlowGraph.getSuccsOf(var);
    }

    public Map<CSVar, List<CustomSink>> potentialResults = new HashMap<>();

    Solver(AnalysisOptions options, HeapModel heapModel, ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
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
//        System.err.println("Add reachable: " + csMethod.getMethod());
        callGraph.addReachableMethod(csMethod);
        StmtVisitor<Void> stmtVisitor = new StmtProcessor(csMethod);
        csMethod.getMethod().getIR().stmts().forEach(stmt -> {
            stmt.accept(stmtVisitor);
        });
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
            Var lv = stmt.getLValue();
            Obj obj = heapModel.getObj(stmt);
            Context ctx = contextSelector.selectHeapContext(csMethod, obj);
            CSVar lsv = csManager.getCSVar(context, lv);
            CSObj csObj = csManager.getCSObj(ctx, obj);
            workList.addEntry(lsv, PointsToSetFactory.make(csObj));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            CSVar lv = csManager.getCSVar(context, stmt.getLValue());
            CSVar rv = csManager.getCSVar(context, stmt.getRValue());
            addPFGEdge(rv, lv);
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            InvokeExp exp = stmt.getInvokeExp();
            CSCallSite cscs = csManager.getCSCallSite(context, stmt);
            if (stmt.isStatic()) {
                JMethod callee = exp.getMethodRef().resolve();
                Context mCtx = contextSelector.selectContext(cscs, callee);
                CSMethod csm = csManager.getCSMethod(mCtx, callee);
                if (!callGraph.addEdge(new Edge<>(resolveKind(stmt), cscs, csm))) return null;

                if (stmt.getResult() != null && taintAnalysis.isSource(callee, stmt.getResult().getType())) {
                    // taint source
                    Obj obj = taintAnalysis.makeTaint(stmt, stmt.getResult().getType());
                    Context objCtx = taintAnalysis.getTaintObjContext(obj);
                    workList.addEntry(
                            csManager.getCSVar(context, stmt.getResult()),
                            PointsToSetFactory.make(csManager.getCSObj(objCtx, obj))
                    );
                }
                processArgs(cscs, csm, null, null);
                return null;
            }
            return null;
        }


        @Override
        public Void visit(LoadField stmt) {
            // y = x.f
            if (!stmt.isStatic())
                return null;
            Var lv = stmt.getLValue();
            JField field = stmt.getFieldAccess().getFieldRef().resolve();
            StaticField sf = csManager.getStaticField(field);
            addPFGEdge(
                    sf, // source
                    csManager.getCSVar(context, lv) // target
            );
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            // x.f = y
            if (!stmt.isStatic()) return null;
            Var rv = stmt.getRValue();
            JField field = stmt.getFieldAccess().getFieldRef().resolve();
            StaticField sf = csManager.getStaticField(field);
            addPFGEdge(
                    csManager.getCSVar(context, rv), // source
                    sf // target
            );
            return null;
        }

        @Override
        public Void visit(StoreArray stmt) {
            // x[i] = y
            Var rv = stmt.getRValue();
            addPFGEdge(
                    csManager.getCSVar(context, rv), // source
                    csManager.getCSVar(context, stmt.getLValue().getBase()) // target
            );
            return null;
        }

        @Override
        public Void visit(LoadArray stmt) {
            // y = x[i]
            Var lv = stmt.getLValue();
            addPFGEdge(
                    csManager.getCSVar(context, stmt.getRValue().getBase()), // source
                    csManager.getCSVar(context, lv) // target
            );
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (source == null || target == null) return;
        if (!pointerFlowGraph.addEdge(source, target)) return;
        if (source.toString().contains("/%this") && target.toString().contains("/temp$2"))
            System.err.println("Add edge: " + source + " -> " + target);
        workList.addEntry(target, source.getPointsToSet());
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry e = workList.pollEntry();
            Pointer ptr = e.pointer();
            PointsToSet pts = e.pointsToSet();

            PointsToSet objs = propagate(ptr, pts);
            if (objs.isEmpty()) continue;
            pointerFlowGraph.getSuccsOf(ptr).forEach(succ -> {
                workList.addEntry(succ, objs);
            });
            if (!(ptr instanceof CSVar csvar)) continue;
            Context ctx = csvar.getContext();
            objs.forEach(csObj -> {
                csvar.getVar().getLoadFields().forEach(loadField -> {
                    JField field = loadField.getFieldAccess().getFieldRef().resolve();
                    addPFGEdge(
                            csManager.getInstanceField(csObj, field),
                            csManager.getCSVar(ctx, loadField.getLValue())
                    );
                });

                csvar.getVar().getStoreFields().forEach(storeField -> {
                    JField field = storeField.getFieldAccess().getFieldRef().resolve();
                    addPFGEdge(
                            csManager.getCSVar(ctx, storeField.getRValue()),
                            csManager.getInstanceField(csObj, field)
                    );
                });

                csvar.getVar().getStoreArrays().forEach(storeArray -> {
                    // x[i] = y
                    // y -> x[i]
                    addPFGEdge(
                            csManager.getCSVar(ctx, storeArray.getRValue()),
                            csManager.getArrayIndex(csObj)
                    );
                });

                csvar.getVar().getLoadArrays().forEach(loadArray -> {
                    addPFGEdge(
                            csManager.getArrayIndex(csObj),
                            csManager.getCSVar(ctx, loadArray.getLValue())
                    );
                });

                processCall(csvar, csObj);
            });
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        //                        target       <-- source
        PointsToSet old = pointer.getPointsToSet();
        PointsToSet diff = PointsToSetFactory.make();
        pointsToSet.forEach(obj -> {
            if (old.contains(obj)) return;
            obj = taintAnalysis.makeTaint(obj, pointer);
            old.addObject(obj);
            diff.addObject(obj);
        });
        return diff;
    }


    private void processArgs(CSCallSite caller,
                             CSMethod callee,
                             CSVar recv,
                             CSObj recvObj) {
        List<Var> args = caller.getCallSite().getInvokeExp().getArgs();
        List<Var> params = callee.getMethod().getIR().getParams();
        CSVar result = null;
        if (caller.getCallSite().getLValue() != null) {
            result = csManager.getCSVar(caller.getContext(), caller.getCallSite().getLValue());
        }
        JMethod calleeMethod = callee.getMethod();
        boolean isSinkPoint = false;
        boolean anyShouldTransfer = false;

        for (int i = 0; i < args.size(); i++) {
            if (taintAnalysis.isSink(calleeMethod, i)) {
                // 在callSite处，第i个参数是sink，记录实参和调用点
                potentialResults.computeIfAbsent(
                                csManager.getCSVar(caller.getContext(), args.get(i)),
                                k -> new ArrayList<>())
                        .add(new CustomSink(caller.getCallSite(), i));
                isSinkPoint = true;
                continue;
            }
            // process taint transfer
            CSVar arg = csManager.getCSVar(caller.getContext(), args.get(i));
            if (recv != null) {
                if (taintAnalysis.shouldTransfer(
                        calleeMethod,
                        i,
                        -1,
                        recv.getType()
                )) {
                    anyShouldTransfer = true;
                    addPFGEdge(arg, recv); // arg -> base
                }
            }
            if (result != null && taintAnalysis.shouldTransfer(
                    calleeMethod,
                    i,
                    -2,
                    result.getType())) {
                anyShouldTransfer = true;
                addPFGEdge(arg, result); // arg -> result
            }
        }

        if (isSinkPoint) return;

        if (result != null && taintAnalysis.shouldTransfer(
                calleeMethod,
                -1,
                -2,
                result.getType())
        ) {
            addPFGEdge(recv, result); // base -> result
            anyShouldTransfer = true;
        }

        if (anyShouldTransfer) {
            System.err.printf("Skip call: %s\n\t%s\n\t%s\n", calleeMethod, recv, recvObj);
            return;
        }

        addReachable(callee);
        for (int i = 0; i < args.size(); i++) {
            addPFGEdge(
                    csManager.getCSVar(caller.getContext(), args.get(i)),
                    csManager.getCSVar(callee.getContext(), params.get(i))
            );
        }
        Var target = caller.getCallSite().getLValue();
        if (target == null) return;
        List<Var> rets = callee.getMethod().getIR().getReturnVars();
        rets.forEach(ret -> {
//            if (ret.toString().equals("%this")) return;
            addPFGEdge(
                    csManager.getCSVar(callee.getContext(), ret),
                    csManager.getCSVar(caller.getContext(), target)
            );
        });

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
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        recv.getVar().getInvokes().forEach(iv -> {
            // recv.m()
            // callerCtx == recv.getContext()
            // recvObj == &obj
            JMethod callee = resolveCallee(recvObj, iv);
            if (callee == null) return;
            CSCallSite callSite = csManager.getCSCallSite(recv.getContext(), iv);
            Context calleeCtx = contextSelector.selectContext(callSite, recvObj, callee);
            CSMethod csCallee = csManager.getCSMethod(calleeCtx, callee);

            // this <-- recvObj
            workList.addEntry(
                    csManager.getCSVar(calleeCtx, callee.getIR().getThis()),
                    PointsToSetFactory.make(recvObj)
            );

            if (!callGraph.addEdge(
                    new Edge<>(
                            resolveKind(iv),
                            callSite,
                            csCallee
                    )
            )) return;
            processArgs(callSite, csCallee, recv, recvObj);
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

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
