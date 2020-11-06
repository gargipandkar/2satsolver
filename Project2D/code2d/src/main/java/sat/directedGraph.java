package sat;

import immutable.ImList;
import immutable.ImMap;

import sat.env.*;
import sat.formula.*;

import java.lang.reflect.Array;
import java.sql.SQLOutput;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

public class directedGraph {
    private HashMap<Literal,Bool> literalValues = new HashMap<>(); ///values of each literal (to be returned at end of function)
    private HashMap<Literal, ArrayList<Literal>> adjacency = new HashMap<>(); ///adjacency matrix of vertices
    private Boolean satisfiable = true; /// update to false if 2-SAT is unsatisfiable
    private HashMap<Literal, Boolean> visited = new HashMap<>(); /// HashMap to keep track of visited vertices in two passes of Kosaraju's DFS
    private Stack<Literal> S = new Stack<>(); ///stack to be used for the two passes of Kosaraju's DFS
    private ArrayList<HashMap<Literal, Bool>> SCC = new ArrayList<>(); ///ArrayList containing each SCC in the graph

    ///clone  a directedGraph for transposing purposes
    public directedGraph(HashMap<Literal,Bool> literalValues){
        this.literalValues = literalValues;
    }

    public directedGraph(Formula formula){

        ImList<Clause> cl_ls = formula.getClauses();

        for(Clause c : cl_ls){
            //if clause contains literal and its negation
            if (c.contains(PosLiteral.make("contradiction"))){
                satisfiable = false ;
            }

            ///if clause contains zero literal or more than two literals
            if(c.isEmpty() || c.size()>2){
                System.out.println("INVALID FORMULA");
                satisfiable = false ;
            }

            ///if clause only contains one literal, treat as (a v a), generate !a-->a only
            if (c.size()==1){
                Literal lit1 = c.chooseLiteral();
                Literal nlit1 = lit1.getNegation();

                literalValues.putIfAbsent(lit1,null);
                literalValues.putIfAbsent(nlit1,null);

                ArrayList<Literal> neighbors = adjacency.get(nlit1);
                if (neighbors == null){
                    neighbors = new ArrayList<Literal>();
                }
                neighbors.add(lit1);
                adjacency.put(nlit1,neighbors);
            }
            ///if clause contains two literals (a v b), generate !a-->b and !b-->a
            if (c.size()==2){
                Iterator<Literal> iter = c.iterator();
                Literal lit1 = iter.next();
                Literal nlit1 = lit1.getNegation();
                Literal lit2 = iter.next();
                Literal nlit2 = lit2.getNegation();

                literalValues.putIfAbsent(lit1,null);
                literalValues.putIfAbsent(nlit1,null);
                literalValues.putIfAbsent(lit2,null);
                literalValues.putIfAbsent(nlit2,null);


                ArrayList<Literal> neighbors1 = adjacency.get(nlit1);

                if (neighbors1 == null){
                    neighbors1 = new ArrayList<Literal>();
                }
                neighbors1.add(lit2);
                adjacency.put(nlit1,neighbors1);

                ArrayList<Literal> neighbors2 = adjacency.get(nlit2);
                if (neighbors2 == null){
                    neighbors2 = new ArrayList<Literal>();
                }
                neighbors2.add(lit1);
                adjacency.put(nlit2,neighbors2);

            }
        }
    }

    public HashMap<Literal, Bool> isSatisfiable(Formula formula){

        generateSCC(this);

        //System.out.println(SCC);

        for (HashMap<Literal, Bool> component: this.SCC){
            for(Literal literal: component.keySet()){
                Literal negliteral = literal.getNegation();
                if (component.containsKey(negliteral))
                    satisfiable = false;
            }
        }

        if (!satisfiable){
            System.out.println("UNSATISFIABLE");
            return null;
        }
        System.out.println("SATISFIABLE");
        this.getSolution();


        //System.out.println(this.adjacency);
        //System.out.println(this.transpose().adjacency);

        return literalValues;
    }

    ///check if it's first pass or second pass of Kosaraju's algorithm
    public void DFSType (directedGraph graph, Boolean isFirstPass){
        ///run through all literal in the directed graph, run DFS if it hasn't been visited and update visited
        for (Literal l:graph.literalValues.keySet()){
            if (graph.visited.get(l)==null){
                graph.visited.put(l,true);
                traverseDFS(graph, isFirstPass, l);
                //System.out.println(graph.visited);
            }
        }
    }

    public void traverseDFS (directedGraph graph, Boolean isFirstPass, Literal l){

        ///if second pass, update SCC
        if (!isFirstPass){
            HashMap<Literal, Bool> innerSCC = SCC.get(SCC.size()-1);
            innerSCC.put(l,Bool.UNDEFINED);
        }

        ///if no more neighbors, return
        ArrayList<Literal> neighbors = graph.adjacency.get(l);
        if (neighbors==null){
            if (isFirstPass){
                S.push(l);
            }
            return;
        }

        ///standard DFS, update visited and visit neighbors
        for (Literal neighbor:neighbors){
            if (graph.visited.get(neighbor)==null){
                graph.visited.put(neighbor,true);
                traverseDFS(graph, isFirstPass ,neighbor);
            }
        }

        ///if first pass, update stack
        if (isFirstPass) {
            S.push(l);
        }


    }

    ///method to generate SCC
    public void generateSCC(directedGraph graph){

        //get DFS and clear SCC and visited to prepare for second pass of Kosaraju's algorithm
        this.DFSType(this,true);
        directedGraph transposed = this.transpose();

        SCC.clear();
        visited.clear();


        ///generate SCC one by one for each member of stack
        while(!S.empty()){
            Literal l = S.pop();

            if (transposed.visited.get(l)==null){
                transposed.visited.put(l,true);
                SCC.add(new HashMap<Literal, Bool>()); ///allocate memory for new SCC
                traverseDFS(transposed, false, l);
            }
        }
    }

    public directedGraph transpose(){
        directedGraph transposed = new directedGraph(this.literalValues);

        ///run through all literal in the graph
        for (Literal l:literalValues.keySet()){
            ArrayList<Literal> neighbors = this.adjacency.get(l);

            ///as long as literal has neighbors
            if (neighbors!=null){
                ///for all the neighbors, add current literal to its adjacency matrix
                for (Literal neighbor:neighbors){
                    ArrayList<Literal> neighborAdjacency = transposed.adjacency.get(neighbor);
                    if (neighborAdjacency == null){
                        neighborAdjacency = new ArrayList<Literal>();
                    }
                    neighborAdjacency.add(l);
                    transposed.adjacency.put(neighbor,neighborAdjacency);
                }
            }
        }
        return transposed;

    }


    public void getSolution(){
        for (int i = SCC.size()-1; i >= 1; i--){
            for (Literal literal : SCC.get(i).keySet()){
                if (literalValues.containsKey(literal)){
                    literalValues.put(literal, Bool.TRUE);
                    literalValues.put(literal.getNegation(), Bool.FALSE);
                }
            }
        }


        for (Literal lit : literalValues.keySet()) {
            System.out.print(lit + " = " + literalValues.get(lit) + " ");
        }
        System.out.println();
    }
}
