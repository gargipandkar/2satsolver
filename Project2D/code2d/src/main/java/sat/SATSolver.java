package sat;

import immutable.EmptyImList;
import immutable.ImList;
import sat.env.Environment;
import sat.formula.Clause;
import sat.formula.Formula;
import sat.formula.Literal;
import sat.formula.PosLiteral;
/*
2D Team 34
Team members
- Gargi Pandkar - 1004680
- Joshua Dean Samjaya - 1004423
- Mihir Chhiber - 1004359
- Ong Li Wen - 1004663
- Pang Bang Yong - 1004486
- Wang Han - 1004520
*/
public class SATSolver {

    public static Environment solve(Formula formula) {

        ImList<Clause> cl_ls = formula.getClauses(); // converting formula into a list of clauses
        Environment env = new Environment(); // initializing environment variable
        return solve(cl_ls, env); // call overloaded function solve with two parameters(clauses and  env)
    }

    private static Environment solve(ImList<Clause> clauses, Environment env) {

        // if there are no clauses in the function, therefore there are no clauses to be solved
        // which means CNF is solvable, return the environment
        if (clauses.isEmpty()) {
            return env;
        }

        // When clause list is empty, which means there is no literal in the clause which can
        // make the clause true, therefore CNF is unsolvable, return env
        for (Clause c : clauses) {
            if (c.isEmpty()) {
                return null;
            }
        }

        Clause small_c = new Clause();
        int small_val = 2147483647; //maximum value for integer in java
        //find the smallest clause in the clause list
        for (Clause clause : clauses) {
            if (clause.size() < small_val) {
                small_val = clause.size();
                small_c = clause;
                if (small_val == 1) { //if clause has only one literal, that is the smallest clause
                    Literal lit = small_c.chooseLiteral(); // store literal from the clause list
                    if (lit instanceof PosLiteral) { //if literal is positive literal
                        // assign True to the literal value in the environment and call
                        // substitute to make the changes in the clause list based on the literal
                        // call solve with parameters as new clause list and new environment
                        // variable and return its output
                        return solve(substitute(clauses, lit), env.putTrue(lit.getVariable()));
                    } else {
                        // assign False to the literal value in the environment and call
                        // substitute to make the changes in the clause list based on the literal
                        // call solve with parameters as new clause list and new environment
                        // variable and return its output
                        return solve(substitute(clauses, lit), env.putFalse(lit.getVariable()));
                    }
                }
            }

        }
        // the block of code down below is executed if the smallest clause has size > 1
        Literal lit = small_c.chooseLiteral(); // store literal from the clause list
        Environment output;
        if (lit instanceof PosLiteral) {
            // assign True to the literal value in the environment and call
            // substitute to make the changes in the clause list based on the literal
            // call solve with parameters as new clause list and new environment
            // variable and return its output
            output = solve(substitute(clauses, lit), env.putTrue(lit.getVariable()));
        } else {
            // assign False to the literal value in the environment and call
            // substitute to make the changes in the clause list based on the literal
            // call solve with parameters as new clause list and new environment
            // variable and return its output
            output = solve(substitute(clauses, lit), env.putFalse(lit.getVariable()));
        }
        // if CNF is not solvable with the previous value of literal, assign opposite value to the
        // literal to check
        if (output == null) {
            lit = lit.getNegation(); // store the negation of the literal and use it
            if (lit instanceof PosLiteral) {
                // assign False to the literal value in the environment and call
                // substitute to make the changes in the clause list based on the literal
                // call solve with parameters as new clause list and new environment
                // variable and return its output
                return solve(substitute(clauses, lit), env.putFalse(lit.getVariable()));
            } else {
                // assign True to the literal value in the environment and call
                // substitute to make the changes in the clause list based on the literal
                // call solve with parameters as new clause list and new environment
                // variable and return its output
                return solve(substitute(clauses, lit), env.putTrue(lit.getVariable()));
            }
        }
        return output;
    }

    private static ImList<Clause> substitute(ImList<Clause> clauses, Literal l) {

        ImList<Clause> new_c_ls = new EmptyImList<Clause>(); // create a new clause list

        for(Clause c: clauses){
            // if literals negation is in clause, returns clause without the literal
            if (c.contains(l.getNegation()) || c.contains(l)) {
                // if the literal is in clause, therefore returns null as its true
                // otherwise removes the literal from the clause and returns the new clause
                c = c.reduce(l);
            }
            // if clause is not null which means clause is not satisfied, store it in the new
            // clause list
            if(c!=null){
                new_c_ls = new_c_ls.add(c);
            }
        }

        return new_c_ls; //return the new clause list
    }

}