package sat;

import immutable.ImList;
import sat.env.*;
import sat.formula.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Random;


/*
let A be a random assignment to the n variables of formula F
repeat for MAX_FLIPS times:
    if F is satisfiable by A
        print “SATISFIABLE”
    else
        pick a clause c that is not satisfied by A
        pick a variable v in c at random
        flip the value of v in A
end repeat
print “UNSATISFIABLE”

*/

public class randomWalk {

    private int maxFlips=100;
    private Random randomGen = new Random();

    public class Assignment {

        private HashMap<Literal, Bool> literalValues = new HashMap<>();

        public Assignment() {
        }

        public Assignment(Map<Literal, Bool> values) {
            literalValues.putAll(values);
        }
        

        public boolean isTrue(Literal literal) {
            return Bool.TRUE.equals(literalValues.get(literal));
        }

        public boolean isFalse(Literal literal) {
            return Bool.FALSE.equals(literalValues.get(literal));
        }

        public Assignment union(Literal literal, Bool boole) {
            Assignment A = new Assignment();
            A.literalValues.putAll(this.literalValues);
            A.literalValues.put(literal, boole);
            return A;
        }
        

        public Assignment flip(Literal literal) {
            /*if (isTrue(literal)) {
                return union(literal, Bool.FALSE);
            } 
            if (isFalse(literal)) {
                return union(literal, Bool.TRUE);
            }
            return this;
            */

            Bool currValue=this.literalValues.get(literal);
            this.literalValues.put(literal, currValue.not());
            Literal negLiteral = literal.getNegation();
            if (this.literalValues.containsKey(negLiteral))
                this.literalValues.put(negLiteral, currValue);
            return this;
        }

        
        public boolean satisfies(ImList<Clause> clauses) {
            for (Clause c : clauses) {
                ArrayList<Literal> clauseLiterals = new ArrayList<>();
                Iterator<Literal> iter = c.iterator();
                Literal lit1 = iter.next();
                Literal lit2 = iter.next();
                /*
                System.out.println("Clause "+c);
                System.out.print(literalValues.get(lit1));
                System.out.println(literalValues.get(lit2));
                System.out.println("Check "+checkClause(c));
                */
                if (!checkClause(c)) {
                    return false;
                }
            }
            return true;
        }
        
        public boolean checkClause(Clause c) {
            ArrayList<Literal> clauseLiterals = new ArrayList<>();
            Iterator<Literal> iter = c.iterator();
            Literal lit1 = iter.next();
            Literal lit2 = iter.next();
            clauseLiterals.add(lit1);
            clauseLiterals.add(lit2);
            
            /*
            boolean clauseEvalTrue = false;
            if (lit1.getNegation().equals(lit2))
                clauseEvalTrue=true;
            for (Literal lit: clauseLiterals){
                if (lit instanceof PosLiteral && literalValues.get(lit)==Bool.TRUE)
                    clauseEvalTrue=true;
                else if (lit instanceof NegLiteral && literalValues.get(lit )==Bool.FALSE)
                    clauseEvalTrue=true;
            }

            Boolean result = null;
            if (clauseEvalTrue) {
                result = Boolean.TRUE;
            } else if (c.isEmpty()) {
                result = Boolean.FALSE;
            } else {
                boolean unassignedLiterals = false;
                Bool value;

                for (Literal literal : clauseLiterals) {
                    value = literalValues.get(literal);
                    if (value != null) {
                        if (Bool.TRUE.equals(value)) {
                            result = Boolean.TRUE;
                            break;
                        }
                    } else {
                        unassignedLiterals = true;
                    }
                }

                if (result == null) {
                    if (!unassignedLiterals) {
                        result = Boolean.FALSE;
                    }
                }

            }
            */
            boolean evalTo=false;
            if ((literalValues.get(lit1).equals(Bool.TRUE)) || (literalValues.get(lit2).equals(Bool.TRUE)))
                evalTo=true;
            return evalTo;
        }

        public void print() {
            for (Map.Entry<Literal, Bool> e : literalValues.entrySet()) {
                System.out.print(e.getKey() + " = " + e.getValue() + " ");
            }
            System.out.println();
        }

        @Override
        public String toString() {
            return literalValues.toString();
        }

        public int variableCount(){
            return literalValues.size();
        }
    }
    
    public boolean isSatisfiable(Formula formula) {
        ImList<Clause> clauses = formula.getClauses();
        Assignment sat = walk(clauses, this.maxFlips); //default maxFlips to 100
        return (sat != null);
    }

    private Assignment walk(ImList<Clause> clauses, int maxFlips) {

        // A is a random assignment of true/false to the literals in clauses
        Assignment A = assignValues(clauses);
        int n = A.variableCount();

        //empty formula
        if (clauses.isEmpty()) {
            System.out.println("INVALID FORMULA");
            return null;
        }

        //not a 2-SAT problem or a clause contains literal and its negation
        for (Clause c: clauses) {
            if (c.size() != 2) {
                System.out.println("INVALID FORMULA");
                return null;
            }

            if (c.contains(PosLiteral.make("contradiction"))){
                System.out.println("UNSATISFIABLE");
                return null;
            }
        }


        for (int i = 0; i < maxFlips*n*n; i++) {
            // if A satisfies clauses then return A
            if (A.satisfies(clauses)) {
                System.out.println("SATISFIABLE");
                A.print();
                return A;
            }

            else {
                Clause clause = selectFalseClause(clauses, A);
                A = A.flip(selectLiteral(clause));
            }
        }
        System.out.println("UNSATISFIABLE");
        return null;
    }

    private Assignment assignValues(ImList<Clause> clauses) {
        // Collect all the literals from all the clauses
        Map<Literal,Bool> literalValues = new HashMap<>();
        for (Clause c : clauses) {
            Iterator<Literal> iter = c.iterator();
            Literal lit1 = iter.next();
            Literal lit2 = iter.next();
            literalValues.putIfAbsent(lit1,null);
            literalValues.putIfAbsent(lit2,null);
        }

        // Make initial guess
        for (Literal literal : literalValues.keySet()) {
            Bool value;
            if (randomGen.nextBoolean())
                value = Bool.TRUE;
            else
                value = Bool.FALSE;
            literalValues.put(literal, value);
        }

        for (Literal literal : literalValues.keySet()) {
            Bool currValue=literalValues.get(literal);
            if (literalValues.containsKey(literal.getNegation())){
                if (currValue.equals(literalValues.get(literal.getNegation())))
                    literalValues.put(literal, currValue.not());
            }
        }

        return new Assignment(literalValues);
    }

    private Clause selectFalseClause(ImList<Clause> allClauses, Assignment A) {
        // Collect the clauses that are false in A
        List<Clause> falseClauses = new ArrayList<>();
        for (Clause c : allClauses) {
            if (Boolean.FALSE.equals(A.checkClause(c))) {
                falseClauses.add(c);
            }
        }

        // Randomly selected clause from list of false clauses
       return falseClauses.get(randomGen.nextInt(falseClauses.size()));
    }

    private Literal selectLiteral(Clause c) {
        ArrayList<Literal> clauseLiterals = new ArrayList<>();
        Iterator<Literal> iter = c.iterator();
        Literal lit1 = iter.next();
        Literal lit2 = iter.next();
        clauseLiterals.add(lit1);
        clauseLiterals.add(lit2);

        // Randomly selected literal from clause
        return (new ArrayList<>(clauseLiterals)).get(randomGen.nextInt(clauseLiterals.size()));
    }

}
