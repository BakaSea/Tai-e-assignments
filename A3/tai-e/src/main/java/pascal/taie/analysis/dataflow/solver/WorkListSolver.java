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
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.ArrayDeque;
import java.util.Queue;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        Queue<Node> workList = new ArrayDeque<>();
        for (Node node : cfg) {
            workList.add(node);
        }
        while (!workList.isEmpty()) {
            Node cur = workList.remove();
            Fact in = analysis.newInitialFact();
            cfg.getPredsOf(cur).forEach(pred -> analysis.meetInto(result.getOutFact(pred), in));
            result.setInFact(cur, in);
            if (analysis.transferNode(cur, in, result.getOutFact(cur))) {
                cfg.getPredsOf(cur).forEach(workList::add);
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        Queue<Node> workList = new ArrayDeque<>();
        for (Node node : cfg) {
            workList.add(node);
        }
        while (!workList.isEmpty()) {
            Node cur = workList.remove();
            Fact out = analysis.newInitialFact();
            cfg.getSuccsOf(cur).forEach(succ -> analysis.meetInto(result.getInFact(succ), out));
            result.setOutFact(cur, out);
            if (analysis.transferNode(cur, result.getInFact(cur), out)) {
                cfg.getPredsOf(cur).forEach(workList::add);
            }
        }
    }
}
