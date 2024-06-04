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
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import pascal.taie.language.type.Type;

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

    public boolean isSource(JMethod method, Type type) {
        return config.getSources().contains(new Source(method, type));
    }

    public boolean isSink(JMethod method, int index) {
        return config.getSinks().contains(new Sink(method, index));
    }

    public boolean isTaint(Obj o) {
        return manager.isTaint(o);
    }

    public boolean isTaint(CSObj o) {
        return manager.isTaint(o.getObject());
    }

    public Obj makeTaint(Invoke source, Type type) {
        return manager.makeTaint(source, type);
    }

    public Obj makeTaint(Obj obj, Type type){
        if (!isTaint(obj)) return obj;
        return manager.makeTaint(manager.getSourceCall(obj), type);
    }

    public CSObj makeTaint(CSObj obj, Pointer p){
        Type type;
        if (p instanceof ArrayIndex)
            type = obj.getObject().getType();
        else
            type = p.getType();
        return csManager.getCSObj(obj.getContext(), makeTaint(obj.getObject(), type));
    }

    public Context getTaintObjContext(Obj obj) {
        return emptyContext;
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        PointerAnalysisResult result = solver.getResult();
        result.storeResult(getClass().getName(), taintFlows);
    }

    public boolean shouldTransfer(JMethod method, int from, int to, Type type) {
        TaintTransfer t = new TaintTransfer(method, from, to, type);
        return config.getTransfers().contains(t);
    }


    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new HashSet<>();
//        System.err.println("================================");
//        solver.getResult().getCSVars().forEach(
//                csVar -> {
////                    if (csVar.getPointsToSet().getObjects().stream().anyMatch(this::isTaint)){
//                    System.err.println("Var: " + csVar + " <- " + solver.getSuccsOf(csVar));
////                    }
//                }
//        );
//        System.err.println("================================");
        solver.getResult().getCSVars().forEach(
                csVar -> {
                    if (csVar.getPointsToSet().getObjects().stream().anyMatch(this::isTaint)) {
                        System.err.println("TaintedVar: " + csVar);
                    }
                }
        );
        solver.potentialResults.forEach((csvar, sink) -> {
            System.err.println("CSVar: " + csvar);
            System.err.println("PointsToSet: ");
            csvar.getPointsToSet().forEach(obj -> {
                System.err.println("\t" + obj);
            });
            System.err.println("Sink: " + sink);
            csvar.getPointsToSet().forEach(obj -> {
                if (manager.isTaint(obj.getObject())) {
                    Invoke source = manager.getSourceCall(obj.getObject());
                    sink.forEach(s -> {
                        taintFlows.add(new TaintFlow(source, s.invoke(), s.index()));
                    });
                }
            });
        });
        System.err.println("TaintFlows: " + taintFlows);
        return taintFlows;
    }
}
