import com.google.ortools.linearsolver.MPConstraint;
import com.google.ortools.linearsolver.MPObjective;
import com.google.ortools.linearsolver.MPSolver;
import com.google.ortools.linearsolver.MPVariable;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.DimacsReader;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;


import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Scanner;


public class Solver {

    public static String SAT = "Tents : with CNF-SAT";
    public static String LP = "Tents : with ILP";

    public Solver() {
    }

    static {
        System.loadLibrary("jniortools");
    }

    public static void SolveWithLp(String solverType, boolean printModel, boardInput b){
        //b.print_board();
        int[][] board = b.get_board();
        int[] vertical = b.getVertical();
        int[] horizontal = b.getHorizontal();
        int n = board.length;
        MPSolver solver = new MPSolver("TentsLinear", MPSolver.OptimizationProblemType.valueOf(solverType));
        double infinity = MPSolver.infinity();
        MPVariable[][][] vars = new MPVariable[n+2][n+2][4];
        MPConstraint[][] ctree = new MPConstraint[n][n];
        MPConstraint[][] ctent = new MPConstraint[n][n];
        MPConstraint[] rows = new MPConstraint[n];
        MPConstraint[] cols = new MPConstraint[n];
        for(int i = 0; i < n + 2; i ++){
            for(int j = 0; j < n + 2; j++){
                for(int k = 0; k < 4; k++){
                   if((j==0||i==0||j==n+1||i==n+1)||(j==1&&k==0)||(j==n&&k==2)||(i==1&&k==1)||(i==n&&k==3)){
                       vars[i][j][k] = solver.makeIntVar(0,0,"x"+i+","+j+","+k);
                   }
                   else{
                       vars[i][j][k] = solver.makeIntVar(0,1,"x"+i+","+j+","+k);
                   }
                }
            }
        }
        MPObjective objective = solver.objective();
        for(int i = 0; i < n + 2; i ++){
            for(int j = 0; j < n + 2; j++){
                for(int k = 0; k < 4; k++){
                    objective.setCoefficient(vars[i][j][k],1);
                }
            }
        }
        objective.setMaximization();
        for(int i = 1; i <= n; i ++){
            for(int j = 1; j <= n; j++){
                ctree[i-1][j-1] = solver.makeConstraint(board[i-1][j-1],board[i-1][j-1]);
                ctree[i-1][j-1].setCoefficient(vars[i][j+1][0],1);
                ctree[i-1][j-1].setCoefficient(vars[i+1][j][1],1);
                ctree[i-1][j-1].setCoefficient(vars[i][j-1][2],1);
                ctree[i-1][j-1].setCoefficient(vars[i-1][j][3],1);
            }
        }
        for(int i = 1; i <= n; i ++){
            for(int j = 1; j <= n; j++){
                ctent[i-1][j-1] = solver.makeConstraint(0,1);
                for(int k = 0; k < 4; k++){
                    for(int l = 0; l <= 1; l++){
                        for(int m = 0; m <= 1; m++){
                            ctent[i-1][j-1].setCoefficient(vars[i+m][j+l][k], 1);
                        }
                    }
                }
            }
        }
        for(int i = 1; i <= n; i ++){
            rows[i-1] = solver.makeConstraint(vertical[i-1],vertical[i-1]);
            for(int j = 1; j <= n; j++){
                for(int k = 0; k < 4; k++){
                    rows[i-1].setCoefficient(vars[i][j][k],1);
                }
            }
        }
        for(int i = 1; i <= n; i ++){
            cols[i-1] = solver.makeConstraint(horizontal[i-1],horizontal[i-1]);
            for(int j = 1; j <= n; j++){
                for(int k = 0; k < 4; k++){
                    cols[i-1].setCoefficient(vars[j][i][k],1);
                }
            }
        }

        if (printModel) {
            String model = solver.exportModelAsLpFormat(false);
            System.out.println(model);
        }

        final MPSolver.ResultStatus resultStatus = solver.solve();

        if (resultStatus != MPSolver.ResultStatus.OPTIMAL) {
            System.err.println("The problem does not have an optimal solution!");
            return;
        }

        if (!solver.verifySolution(1e-7, true)) {
            System.err.println("The solution returned by the solver violated the"
                    + " problem constraints by at least 1e-7");
            return;
        }

        System.out.println("Problem solved in " + solver.wallTime() + " milliseconds");
        System.out.println("Optimal objective value = " + solver.objective().value());
        /*for(int i = 0; i < n + 2; i ++) {
            for (int j = 0; j < n + 2; j++) {
                for (int k = 0; k < 4; k++) {
                    System.out.println("x" + i + "," + j + "," + k + " = " + vars[i][j][k].solutionValue());
                }
            }
        }*/

        System.out.println(b.adaptSolutionlp(vars));

    }

    public static void SolveWithSAT(final String filename, boardInput b){
        //b.print_board();
        try {
            b.createCNF("myCNF");
        }
        catch (IOException e){
            System.out.println("cannot create example file");
        }
        ISolver solver = SolverFactory.newDefault();
        solver.setTimeout(3600);// 1 hour timeout
        Reader reader = new DimacsReader(solver);
        PrintWriter out = new PrintWriter(System.out,true);
        // CNF filename is given on the command line
        try {
            //b.print_board();
            long stime = System.currentTimeMillis();
            IProblem problem = reader.parseInstance(filename);
            if (problem.isSatisfiable()) {
                System.out.println("Satisfiable !");
                System.out.println(b.adaptSolution(problem.model()));
                long ctime = System.currentTimeMillis();
                System.out.println("Determined in " + (ctime-stime) + " milliseconds");
                // variable check
                /*for (int i=0;i<problem.model().length;i++)
                    System.out.println(problem.model()[i]);
                */
                //b.print_board();
                reader.decode(problem.model(), out);
            }
            else {
                System.out.println("Unsatisfiable !");
            }



        } catch (FileNotFoundException e) {
            // TODO Auto-generated catch block
        } catch (ParseFormatException e) {
            // TODO Auto-generated catch block
        } catch (IOException e) {
            // TODO Auto-generated catch block
        } catch (ContradictionException e) {
            System.out.println("Unsatisfiable (trivial)!");
        } catch (TimeoutException e) {
            System.out.println("Timeout, sorry!");
        }
    }

    public static double treePrecent(int n, int s, int m){
        double sum = 0;
        for(int i = 0; i < m; i++){
            boardInput b = new boardInput(n , s);
            sum = sum + b.treePrecent();
        }

        //System.out.println("Precent of trees on map size " + n + ", with at most " + s + " trees in " + m + " repetitions is " + (double)(sum/m) + "%");
        return (sum/m);
    }
//    public static int[][] treePrecent2(int n, int s, int m){
//        double sum = 0;
//        for(int i = 0; i < m; i++){
//            boardInput b = new boardInput(n , s);
//            sum = sum + b.treePrecent();
//        }
//
//        System.out.println("Precent of trees on map size " + n + ", with at most " + s + " trees in " + m + " repetitions is " + (double)(sum/m) + "%");
//    }

    public static double[] stat_array(int max_size, int ManyMapsYouwant) {
        double[] a = new double[max_size - 1];
        for(int i = 2;i <= max_size ; i++){
            a[i-2] = treePrecent(i,i*i/2,ManyMapsYouwant);
        }
        return a;
    }
    public static void RunSolvers(String[] args,boolean GUIp){
        boardInput b;
        Scanner in = new Scanner(System.in);
        int mode = 0;
        int n = 0;
        int s = 0;
        int m = 0;
        while(true) {
            System.out.println("Please choose: SAT - 0, LP - 1, Statistics - 2, Or Exit - 3");
            mode = in.nextInt();
            if(mode == 3){
                System.out.println("Exiting \u2639");
                System.exit(1);
            }
            System.out.println("Please choose the size of the map:");
            n = in.nextInt();
            System.out.println("Please choose the amount of trees to place in the map:");
            s = in.nextInt();
            if(mode == 2){
                System.out.println("Please choose the amount of maps for the statistics:");
                m = in.nextInt();
                treePrecent(n,s,m);
            }
            b = new boardInput(n, s);
            b.print_board();
            if(mode == 0){
                if(GUIp)
                    b.printGUI_board(SAT);
                else
                    b.print_board();

                SolveWithSAT(args[0], b);

                if(GUIp)
                    b.printGUI_board(SAT);
                else
                    b.print_board();
            }
            if(mode == 1){
                if(GUIp)
                    b.printGUI_board(LP);
                else
                    b.print_board();

                SolveWithLp("BOP_INTEGER_PROGRAMMING", false, b);

                if(GUIp)
                    b.printGUI_board(LP);
                else
                    b.print_board();
            }
            //b.print_board();
        }

    }


    public static void main(String[] args) {;

        //System.out.println(System.getProperty("java.library.path"));
        boardInput b1 = new boardInput(4);
        int[] lemala = {0,1,0,1};
        int[] smola = {0,2,0,0};
        int[][] luach = {{0,0,0,0},
                         {1,0,1,0},
                         {0,0,0,0},
                         {0,0,0,0}};
        int[][] luach2 = {{0,0,0,0},
                {0,1,0,0},
                {0,0,0,0},
                {0,1,0,0}};
        boardInput b = new boardInput(4, smola, lemala, luach);
        boardInput b20 = new boardInput(4, smola, lemala, luach2);
       // boardInput b2 = new boardInput(4, 12);
        //b2.print_board();
        //b2.printGUI_board();
        RunSolvers(args,true);
        //double[] a = stat_array(120, 10);
        //for(int i = 0;i < a.length; i++)
        //    System.out.println(a[i]);


    }
}
