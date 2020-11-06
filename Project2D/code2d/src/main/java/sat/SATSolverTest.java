package sat;

/*
import static org.junit.Assert.*;
import org.junit.Test;
*/

import sat.env.*;
import sat.formula.*;

// additional import
import java.io.File; // import File class
import java.io.FileNotFoundException; // import this class to handle error
import java.io.FileWriter;
import java.io.IOException; // import this class to handle error
import java.util.Scanner; // import Scanner to read text files
import java.util.Arrays;

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

/*
Solve 2-SAT problem using either randomWalk algorithm or directedGraph algorithm
Arguments: <filepath> <algorithm name>
Outputs:
    2-SAT Solver <algorithm name>
    <SATISFIABLE/UNSATISFIABLE>
    <solution>

 */

public class SATSolverTest {
    Literal a = PosLiteral.make("a");
    Literal b = PosLiteral.make("b");
    Literal c = PosLiteral.make("c");
    Literal na = a.getNegation();
    Literal nb = b.getNegation();
    Literal nc = c.getNegation();

    public static void main(String[] args) {
        // Main method that reads the .cnf file
        // Calls SATSolver.solve to determine the satisfiability
        // If SATSolver.solve is satisfiable, variable and its assignment are written to file "BoolAssignment.txt". To create the file, call CreateFile method()
        // If SATSolver.solve is not satisfiable, return "Formula is not satisfiable"

        if (args.length < 1) {
            System.out.println("No file provided");
            System.exit(1);
        }

        String filename = args[0];
        String algo=null;
        if (args.length>1)
            algo = args[1];

        Formula f2 = ReadFile(filename);

        //2-SAT Solver
        if (algo!=null){
            System.out.print("2-SAT Solver ");
            System.out.println(algo);
            if (algo.equals("directedGraph")){
                directedGraph DG = new directedGraph(f2);
                DG.isSatisfiable(f2);
            }
            else if (algo.equals("randomWalk")){
                randomWalk RW = new randomWalk();
                RW.isSatisfiable(f2);
            }
            else
                System.out.println("Algorithm not defined");
        }

        //IGNORE - DPLL SAT-Solver
        else {
            System.out.println("DPLL");
            long started = System.nanoTime();
            Environment e = SATSolver.solve(f2);
            long time = System.nanoTime();
            long timeTaken = time - started;

            if (e != null) {
                String env = e.toString();
                if (env.compareTo("Environment:[]") == 0) {
                    System.out.println("not satisfiable");
                } else {
                    System.out.println("satisfiable");
                    FileWriter outputFile = CreateFile(e);
                }
            } else {
                System.out.println("not satisfiable");
            }

            System.out.println("Time:" + timeTaken / 1000000.0 + "ms");
        }

    }

    public static FileWriter CreateFile(Environment env) {
        try {
            // Create file "BoolAssignment.txt" to store all the variables and its assignment
            // For each variable, format it as <variable>:<assignment> in a new line
            // Return file

            File output = new File("BoolAssignment.txt");
            FileWriter writeFile = new FileWriter(output);
            String stringEnv = env.toString().replace("Environment:[", "");
            stringEnv = stringEnv.replace("]", "");
            String[] arrayEnv = stringEnv.split(", ");
            for (String s : arrayEnv) {
                String[] substring = s.split("->");
                writeFile.write(substring[0] + ':' + substring[1] + "\n");
            }
            writeFile.close();
            return writeFile;
        } catch (IOException e) {
            e.printStackTrace();
            return null;
        }
    }

    public static Formula ReadFile(String filename) {
        // Read .cnf file
        try {
            File cnfFile = new File(filename);
            Scanner reader = new Scanner(cnfFile);
            int totalClause = 0;
            boolean read = true;

            // Retrieve the total number of clauses
            while (read == true) {
                String data = reader.nextLine();
                if (data.charAt(0) == 'p') {
                    String[] element = data.split(" ");
                    totalClause = Integer.parseInt(element[Arrays.asList(element).size() - 1]);
                    read = false;
                }
            }

            Clause c = new Clause();
            Formula f = new Formula();

            // Form clauses and formula by reading each line of the cnf file
            while (f.getSize() != totalClause) {
                String data = reader.nextLine();
                if (data.charAt(0) == 'c' || data.charAt(0) == 'p' || data.equals("")) {
                    continue;
                } else {
                    // For every variable in a line of the cnf file, make it to be a Literal type and add into a clause
                    // If variable has a negative sign, remove negative sign then negate and add it to a clause
                    // If variable does not have negative sign, add it to a clause
                    // After all variables in a line is made into a Literal and added to the same clause, add clause into formula and create a new instance of Clause
                    // Return formula
                    String[] element = data.trim().split("\\s+");
                    Literal elements;

                    for (int i = 0; i < element.length; i++) {
                        if (Integer.parseInt(element[i]) < 0) {
                            int removeNeg = Math.abs(Integer.parseInt(element[i]));
                            elements = NegLiteral.make(Integer.toString(removeNeg));
                            c = c.add(elements);
                        } else if (Integer.parseInt(element[i]) > 0) {
                            elements = PosLiteral.make(element[i]);
                            c = c.add(elements);
                        }
                    }
                    f = f.addClause(c);
                    c = new Clause();
                }
            }
            reader.close();
            return f;
        } catch (FileNotFoundException e) {
            e.printStackTrace();
            return null;
        }
    }

    public void testSATSolver1() {
        // (a v b)
        Environment e = SATSolver.solve(makeFm(makeCl(a, b)));
/*
        assertTrue( "one of the literals should be set to true",
                Bool.TRUE == e.get(a.getVariable())
                || Bool.TRUE == e.get(b.getVariable())  );
*/
    }


    public void testSATSolver2() {
        // (~a)
        Environment e = SATSolver.solve(makeFm(makeCl(na)));
/*
        assertEquals( Bool.FALSE, e.get(na.getVariable()));
*/
    }

    private static Formula makeFm(Clause... e) {
        Formula f = new Formula();
        for (Clause c : e) {
            f = f.addClause(c);
        }
        return f;
    }

    private static Clause makeCl(Literal... e) {
        Clause c = new Clause();
        for (Literal l : e) {
            c = c.add(l);
        }
        return c;
    }

}