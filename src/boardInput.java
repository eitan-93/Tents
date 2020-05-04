
import com.google.ortools.linearsolver.MPVariable;

import javax.swing.*;
import java.awt.*;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Arrays;
import java.util.Random;

import static javax.swing.SwingConstants.CENTER;

public class boardInput {
    private int[][] board;
    // board is a matrix of size x size where for all i,j:
    //        board[i][j] = 0 means empty (or " ")
    //        board[i][j] = 1 means tree (or "  \uD83C\uDF32 ")
    //        board[i][j] = 2 means tent (or "  ⛺ ")
    private int[] horizontal_tents;
    // The upper limitations one has
    private int[] vertical_tents;
    // The left limitations one has
    private int size;
    private String treeChar = "  \uD83C\uDF32 ";
    private String tentChar = "  ⛺ ";

    public boardInput(int n) {
        this.size = n;
        this.vertical_tents = new int[n];
        this.horizontal_tents = new int[n];
        this.set_board(this.size);
    }

    public boardInput(int n, int[] vertical_tents, int[] horizontal_tents, int[][] board) {
        this.size = n;
        this.vertical_tents = vertical_tents;
        this.horizontal_tents = horizontal_tents;
        this.board = board;
    }

    public boardInput(int n, int s) {
        this.size = n;
        this.board = new int[n][n];
        this.vertical_tents = new int[n];
        this.horizontal_tents = new int[n];
        for (int i = 0; i < this.size; i++) {
            for (int j = 0; j < this.size; j++) {
                this.board[i][j] = 0;
            }
        }
        for (int i = 0; i < this.size; i++) {
            this.horizontal_tents[i] = 0;
        }
        for (int j = 0; j < this.size; j++) {
            this.vertical_tents[j] = 0;
        }
        int[][][] megaBoard = new int[this.size][this.size][4];
        int sum = 4 * n * n - 4 * n;
        for (int i = 0; i < megaBoard.length; i++) {
            for (int j = 0; j < megaBoard.length; j++) {
                for (int k = -1; k <= 1; k++) {
                    for (int l = -1; l <= 1; l++) {
                        //k = 0, l = -1 smola - 0
                        //k = 0, l = 1 yamina - 2
                        //k = 1, l = 0 lemala - 1
                        //k = -1, l = 0 lemata - 3
                        if ((k * k != l * l) && (i + k >= 0) && (i + k < n) && (j + l >= 0) && (j + l < n)) {
                            megaBoard[i][j][(l + 1) * (k * k - k + 1)] = 1;
                        }
                    }
                }
            }
        }


        int a;
        int b;
        int k;
        int l1 = 0;
        int l2 = 0;


        for (int l = 1; l <= s; l++) {
            a = 0 + (int) (Math.random() * ((this.size - 1 - 0) + 1));
            b = 0 + (int) (Math.random() * ((this.size - 1 - 0) + 1));
            k = 0 + (int) (Math.random() * (4));
            while (sum > 0 && megaBoard[a][b][k] == 0) {
                a = 0 + (int) (Math.random() * ((this.size - 1 - 0) + 1));
                b = 0 + (int) (Math.random() * ((this.size - 1 - 0) + 1));
                k = 0 + (int) (Math.random() * (4));
            }
            if (k == 0) {
                l1 = 0;
                l2 = -1;
            }
            if (k == 1) {
                l1 = 1;
                l2 = 0;
            }
            if (k == 2) {
                l1 = 0;
                l2 = 1;
            }
            if (k == 3) {
                l1 = -1;
                l2 = 0;
            }

            if (megaBoard[a][b][k] == 1 && board[a][b] == 0 && board[a + l1][b + l2] == 0) {
                this.board[a][b] = 1;
                this.board[a + l1][b + l2] = 2;
                this.vertical_tents[a + l1] = this.vertical_tents[a + l1] + 1;
                this.horizontal_tents[b + l2] = this.horizontal_tents[b + l2] + 1;
                /*    for(int m1 = -1; m1 <= 1; m1 = m1+1){
                        for(int m2 = -1; m2 <= 1; m2 = m2+1) {
                            if (m1 * m1 != m2 * m2 && (a+l1+m1>=0)&&(a+l1+m1<this.size)&&(b+l2+m2>=0)&&(b+l2+m2<this.size)) {
                                if (megaBoard[a + l1 + m1][b + l2 + m2][(-m2+1)*(m1*m1+m1+1)] == 1) {
                                    sum = sum - 1;
                                }
                                megaBoard[a + l1 + m1][b + l2 + m2][(-m2+1)*(m1*m1+m1+1)] = 0;
                            }
                        }
                    }
                    for(int r1 = -1; r1 <= 1; r1 = r1+1){
                        for(int r2 = -1; r2 <= 1; r2 = r2+1){
                            for(int t = 0; t <= 3; t++){
                                if((a+r1>=0)&&(a+r1<this.size)&&(b+r2>=0)&&(b+r2<this.size)){
                                    if(megaBoard[a+r1][b+r2][t] == 1){
                                        sum = sum - 1;
                                    }
                                    megaBoard[a+r1][b+r2][t] = 0;
                                }
                            }
                        }
                    }*/
                //for (int e = 0; e < megaBoard.length; e++) {
                //    for (int f = 0; f < megaBoard.length; f++) {
                for (int m1 = -1; m1 <= 1; m1++) {
                    for (int m2 = -1; m2 <= 1; m2++) {
                        if (a + l1 + m1 >= 0 && a + l1 + m1 <= this.size - 1 && b + l2 + m2 >= 0 && b + l2 + m2 <= this.size - 1) {
                            /*for (int o = 0; o <= 3; o++) {
                                if (o == 0) {
                                    if (inMap(a + l1 + m1, b + l2 + m2 - 1) && closeCells(a + l1, b + l2, a + l1 + m1, b + l2 + m2 - 1)) {
                                        if (megaBoard[a + l1 + m1][b + l2 + m2][o] == 1) {
                                            sum = sum - 1;
                                        }
                                        megaBoard[a + l1 + m1][b + l2 + m2][o] = 0;
                                    }
                                }
                                if (o == 1) {
                                    if (inMap(a + l1 + m1 + 1, b + l2 + m2) && closeCells(a + l1, b + l2, a + l1 + m1 + 1, b + l2 + m2)) {
                                        if (megaBoard[a + l1 + m1][b + l2 + m2][o] == 1) {
                                            sum = sum - 1;
                                        }
                                        megaBoard[a + l1 + m1][b + l2 + m2][o] = 0;
                                    }
                                }
                                if (o == 2) {
                                    if (inMap(a + l1 + m1, b + l2 + m2 + 1) && closeCells(a + l1, b + l2, a + l1 + m1, b + l2 + m2 + 1)) {
                                        if (megaBoard[a + l1 + m1][b + l2 + m2][o] == 1) {
                                            sum = sum - 1;
                                        }
                                        megaBoard[a + l1 + m1][b + l2 + m2][o] = 0;
                                    }
                                }
                                if (o == 3) {
                                    if (inMap(a + l1 + m1 - 1, b + l2 + m2) && closeCells(a + l1, b + l2, a + l1 + m1 - 1, b + l2 + m2)) {
                                        if (megaBoard[a + l1 + m1][b + l2 + m2][o] == 1) {
                                            sum = sum - 1;
                                        }
                                        megaBoard[a + l1 + m1][b + l2 + m2][o] = 0;
                                    }
                                }
                            }*/
                            if ((m1 * m1 != m2 * m2) && (megaBoard[a + l1 + m1][b + l2 + m2][(-m2 + 1) * (m1 * m1 + m1 + 1)] == 1)) {
                                sum = sum - 1;
                            }
                            if (m1 * m1 != m2 * m2) {
                                megaBoard[a + l1 + m1][b + l2 + m2][(-m2 + 1) * (m1 * m1 + m1 + 1)] = 0;
                            }
                            for (int r1 = -1; r1 <= 1; r1++) {
                                for (int r2 = -1; r2 <= 1; r2++) {
                                    if ((r1 * r1 != r2 * r2) && (a + l1 + m1 + r1 >= 0) && (a + l1 + m1 + r1 < n) && (b + l2 + m2 + r2 >= 0) && (b + l2 + m2 + r2 < n)) {
                                        if (megaBoard[a + l1 + m1 + r1][b + l2 + m2 + r2][(-r2 + 1) * (r1 * r1 + r1 + 1)] == 1) {
                                            sum = sum - 1;
                                        }
                                        megaBoard[a + l1 + m1 + r1][b + l2 + m2 + r2][(-r2 + 1) * (r1 * r1 + r1 + 1)] = 0;
                                    }
                                }
                            }
                        }
                        //}
                        //}
                    }
                }
            }
        }



        for (int i = 0; i < this.size; i++) {
            for (int j = 0; j < this.size; j++) {
                if (board[i][j] % 2 == 0) {
                    board[i][j] = 0;
                }
            }
        }
    }


    public boolean closeCells(int i1, int j1, int i2, int j2){
        return ((i1<=i2+1)&&(i2<=i1+1)&&(j1<=j2+1)&&(j2<=j1+1));
    }

    public double treePrecent(){
        int treeamount = 0;
        for(int i = 0; i < this.size; i++){
            for(int j = 0; j < this.size; j++){
                if(board[i][j] == 1){
                    treeamount = treeamount + 1;
                }
            }
        }
       return (double)((100*treeamount)/(this.size*this.size));
    }


    private String convertToDraw(int val) {
        return (val == 0) ? " " : (val == 1) ? treeChar : (val == 2) ? tentChar : "error";
    }


    public int[][] get_board() {
        return this.board;
    }

    public int[] getHorizontal(){
        return this.horizontal_tents;
    }

    public int[] getVertical(){
        return this.vertical_tents;
    }

    public void set_board(int n) {
        this.board = new int[n][n];
        int tree_num = 0;

        for (int i = 0; i < n; ++i) {
            for (int j = 0; j < n; ++j) {
                if (tree_num <= n * n / 2 && (new Random()).nextBoolean()) {
                    ++tree_num;
                    this.board[i][j] = 1;
                    ++this.vertical_tents[j];
                    ++this.horizontal_tents[i];
                } else {
                    this.board[i][j] = 0;
                }
            }
        }
        // So far, both horizontal_tents and vertical_tress held the number of trees
        // Now, we want them to hold a random number between 0 and the number of
        // possible tents (which is, size minus the number of trees)
        int i;
        for (i = 0; i < this.size; ++i) {
            this.horizontal_tents[i] = (int) (Math.random() * (double) (this.size - this.horizontal_tents[i] + 1));
            this.vertical_tents[i] = (int) (Math.random() * (double) (this.size - this.vertical_tents[i] + 1));
        }

    }


    public void print_board() {
        int rowLength = this.size * 4 + this.size + 1;
        char[] separator = new char[rowLength];
        char[] spacer = new char[(int) Math.ceil(Math.log10((double) this.size))];
        Arrays.fill(spacer, ' ');
        Arrays.fill(separator, '-');
        System.out.print("   ");

        int i;
        for (i = 0; i < this.horizontal_tents.length; ++i) {
            System.out.printf("%5d", this.horizontal_tents[i]);
        }

        System.out.println();

        for (i = 0; i < this.board.length; ++i) {
            System.out.println("  " + String.valueOf(spacer) + String.valueOf(separator));
            System.out.print(this.vertical_tents[i] + "  ");

            for (int j = 0; j < this.board[i].length; ++j) {
                System.out.printf("|%4s", convertToDraw(this.board[i][j]));
                if (j == this.board[i].length - 1) {
                    System.out.println("|");
                }
            }
        }
        System.out.println("  " + String.valueOf(spacer) + String.valueOf(separator));
    }


    public void printGUI_board(String method){

        JFrame frame = new JFrame(method);
        int framesize = Math.max(200,this.size*100);
        frame.setSize(framesize, framesize);
        JPanel panel = new JPanel();
        panel.setLayout(new GridLayout(this.size+1,this.size+1));

        int[][] tmp = new int[this.size+1][this.size+1];
        for(int t=0;t<tmp.length;t++){
            for(int p = 0;p<tmp[t].length;p++)
            {
                if(t > 0 && p==0)tmp[t][p] = this.vertical_tents[t-1];
                if(t==0 && p>0)tmp[t][p] = this.horizontal_tents[p-1];
                if(t>0 && p>0)tmp[t][p] = this.board[t-1][p-1];
            }
        }

        int i = 0;
        int j = 0;
        String text = "";
        Color c = Color.BLACK;
        for (int k=0; k < (this.size+1)*(this.size+1); k++) {
            //System.out.println(j+" "+i);

            if (k!=0 && k%(this.size+1) == 0){
                j=(j+1)%(this.size+1);
                i = 0;
            }
            if(!(k>0 && k<(this.size+1)) && !(k>0 && k%(this.size+1)==0)) {
                switch (tmp[j][i++]) {
                    case 1:
                        text = "\uD83C\uDF32";
                        c = new Color(0, 153, 0);
                        break;
                    case 2:
                        text = "⛺";
                        c = new Color(204, 204, 0);
                        break;
                    default:
                        text = "";
                        c = Color.BLACK;
                        break;
                }
            }
            else
                text = ""+tmp[j][i++];

            JTextField cell = new JTextField(text);
            cell.setFont(new Font("Segoe UI Symbol", Font.BOLD, 20));
            cell.setPreferredSize(new Dimension(5, 5));
            cell.setForeground(c);
            c = Color.BLACK;
            cell.setHorizontalAlignment(CENTER);
            panel.add(cell);


        }
        frame.setContentPane(panel);
        //frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        frame.setVisible(true);

    }

    public int countTrees() {
        int c = 0;
        for (int i = 0; i < this.size; i++) {
            for (int j = 0; j < this.size; j++) {
                if (this.board[i][j] == 1) {
                    c++;
                }
            }
        }
        return c;
    }

    public int countTents() {
        int c = 0;
        for (int i = 0; i < this.size; i++) {
            for (int j = 0; j < this.size; j++) {
                if (this.board[i][j] == 2) {
                    c++;
                }
            }
        }
        return c;
    }


    private boolean inMap(int index, int jindex) {
        return ( (1<= index) && (index <= this.size) && (1<= jindex) && (jindex <= this.size) );
    }

    private boolean neighbours(int index1, int jindex1, int index2, int jindex2) {
        return ( (index1 == index2 && jindex1 == jindex2-1) || (index1 == index2 && jindex1 == jindex2+1) || (index1 == index2-1 && jindex1 == jindex2) || (index1 == index2+1 && jindex1 == jindex2) );
    }

    public void createCNF() {
        try {
            createCNF("untitled");
        } catch (IOException e) {
            System.out.println("cannot create file");
        }
    }


    // Check if a certain number on any row/column is too big or small
    public boolean tooManyTentsYouWant(){
        for (int i = 0; i < this.size; i++) {
            if ( (this.horizontal_tents[i] >= this.size) || (this.horizontal_tents[i] <0)
                   || (this.vertical_tents[i] >= this.size) || (this.vertical_tents[i] <0)){
                return true;
            }
        }

        return false;
    }


    private int ourLogSquare(){
        return (int)(Math.floor(Math.log(this.size * this.size-1)/Math.log(2))+1);
    }
    private int ourLog(){
        return (int)(Math.floor(Math.log(this.size)/Math.log(2))+1);
    }

    // Converts an integer (positive one) to a string that binarically represents it
    private String createSij(int num){
        String tmpSij = Integer.toBinaryString(num-1);
        //int currentLength = tmpSij.length();
        int wantedLength = ourLogSquare();
        //int diffLength = wantedLength - currentLength;
        String padAmount = "%"+wantedLength+"s";
        return String.format(padAmount, tmpSij).replace(' ', '0');
    }

    private int alpha(int i, int j, int g, int l){
        String sij = createSij((i-1)* this.size + j);
        int mult = -1;
        int logUp = ourLogSquare();
        int aigl = 4 * this.size *this.size * this.size + 8 *this.size * this.size + this.size*(i-1)*logUp + (g-1) * logUp + l;
        if (sij.charAt(l-1) == '1'){
            mult = 1;
        }
        return mult*aigl;
    }

    private int beta(int i, int j, int g, int l){
        String sij = createSij((i-1)* this.size + j);
        int mult = -1;
        int logUp = ourLogSquare();
        int bigl = 4 * this.size *this.size * this.size + this.size*this.size*logUp + 8 *this.size * this.size + this.size*(i-1)*logUp + (g-1) * logUp + l;
        if (sij.charAt(l-1) == '1'){
            mult = 1;
        }
        return mult*bigl;
    }

    private int gamma(int i, int j, int g, int l){
        String sij = createSij((i-1)* this.size + j);
        int mult = -1;
        int logUp = ourLogSquare();
        int cjgl = 4 * this.size *this.size * this.size  + 2*this.size*this.size*logUp+ 8 *this.size * this.size +this.size*(j-1)*logUp + (g-1) * logUp + l;
        if (sij.charAt(l-1) == '1'){
            mult = 1;
        }
        return mult*cjgl;
    }

    private int delta(int i, int j, int g, int l){
        String sij = createSij((i-1)* this.size + j);
        int mult = -1;
        int logUp = ourLogSquare();
        int djgl = 4 * this.size *this.size * this.size + 3*this.size*this.size*logUp+ 8 *this.size * this.size + this.size*(j-1)*logUp + (g-1) * logUp + l;
        if (sij.charAt(l-1) == '1'){
            mult = 1;
        }
        return mult*djgl;
    }

    public void createCNF(String fileName) throws IOException {
        BufferedWriter writer = new BufferedWriter(new FileWriter(fileName + ".cnf"));
        if (tooManyTentsYouWant()){
            System.out.println("Given map cannot be solved due to having at least one row/column \n with a requirement about having ≥ "+this.size+" tents. Please fix and re-run.");
            return;
        }
        // TODO : update when we add new phis.
        int logUpSquare = ourLogSquare();
        int logUp = ourLog();
        int varNumTij = this.size * this.size;
        int varNumOij = this.size * this.size;
        int varNumKij = 4 * this.size * this.size;
        int varNumXik = this.size * this.size;
        int varNumYjk = this.size * this.size;
        int varNumRgij = this.size * this.size * this.size;
        int varNumSgij = this.size * this.size * this.size;
        int varNumMgij = this.size * this.size * this.size;
        int varNumNgij = this.size * this.size * this.size;
        int varNumAjgl = this.size *this.size * logUpSquare;
        int varNumBjgl = this.size*this.size * logUpSquare;
        int varNumCjgl = this.size*this.size * logUpSquare;
        int varNumDjgl = this.size *this.size* logUpSquare;
        int varNUm = varNumTij + varNumOij + varNumKij + varNumXik + varNumYjk + varNumMgij + varNumNgij + varNumAjgl + varNumBjgl + varNumRgij + varNumSgij + varNumCjgl + varNumDjgl;
        int clausNumPhi0 = this.size * this.size + countTents() + 2 * this.size * this.size;
        int clausNumPhi1 = this.size * this.size;
        int clausNumPhi2 = 15 * (this.size - 2) * (this.size - 2) + 40 * (this.size - 2) + 24;
        int clausNumPhi3 = 8 * (this.size -2) * (this.size -2) + 20 * (this.size -2) + 12;
        int clausNumPhi4 = this.size * this.size * this.size * (2 + this.size * logUpSquare);
        clausNumPhi4 = clausNumPhi4 -this.size*this.size*(1+this.size*logUpSquare);
        //clausNumPhi4 = 0;
        int clausNumPhi5 = this.size * this.size * this.size * ( 2 + this.size * logUpSquare);
        clausNumPhi5 = clausNumPhi5 -this.size*this.size*(1 + this.size*logUpSquare);
        //clausNumPhi5 = 0;
        int clausNumPhi6 = 7*(this.size - 2) * (this.size - 2) + 16*(this.size - 2) + 8 ;
        //int clausNumPhi6 = 2 * this.size * (1 + this.size * (this.size - 1));
        int clauseNum = clausNumPhi0 + clausNumPhi1 + clausNumPhi2 + clausNumPhi3  + clausNumPhi4 + clausNumPhi5 + clausNumPhi6;
        String problem = "p cnf " + varNUm + " " + clauseNum + "\n";
        writer.write(problem);
        createPhi0(writer);
        createPhi1(writer);
        createPhi2(writer);
        createPhi3(writer);
        createPhi4(writer);
        createPhi5(writer);
        createPhi6(writer);
        writer.close();
    }

    public void createPhi0(BufferedWriter writer) throws IOException {
        String tmpClause = "";
        int tij = 0;
        for (int i = 1; i <= this.size; i++) {
            for (int j = 1; j <= this.size; j++) {
                if (this.board[i - 1][j - 1] == 1) {
                    tij = (i - 1) * this.size + j;
                    tmpClause = tij + " 0\n";
                    writer.append(tmpClause);
                }
                else
                    {
                     tij = - ((i - 1) * this.size + j);
                     tmpClause = tij + " 0\n";
                     writer.append(tmpClause);

                }
            }
        }


        int oij = 0;
        for (int i = 1; i <= this.size; i++) {
            for (int j = 1; j <= this.size; j++) {
                if (this.board[i - 1][j - 1] == 2) {
                    oij = this.size * this.size + (i - 1) * this.size + j;
                    tmpClause = oij + " 0\n";
                    writer.append(tmpClause);
                }
            }
        }

        //writer.append("c Xik values are:\n");
        
        int xik = 0;
        for (int i = 1; i <= this.size; i++) {
            for (int k=0; k<=this.size - 1; k++) {
                xik = 6 * this.size * this.size + (i - 1) * this.size + k + 1;
                if (vertical_tents[i-1] == k) {
                    tmpClause = xik + " 0\n";
                }
                else {
                    tmpClause = -xik + " 0\n";
                }
                //writer.append("c X"+i+","+k+" is: \n");
                writer.append(tmpClause);
            }
        }
        //writer.append("c End of Xik values!\n");
        
        int yjk = 0;
        for (int j = 1; j <= this.size; j++) {
            for (int k = 0; k <= this.size - 1; k++) {
                yjk = 7*this.size*this.size + (j-1)*this.size + k + 1;
                if (horizontal_tents[j-1] == k) {
                    tmpClause = yjk + " 0\n";
                }
                else {
                    tmpClause = -yjk + " 0\n";
                }
                writer.append(tmpClause);
            }
        }
        // Test: Forcefully make
//        writer.append("18 0\n");
    }

    public void createPhi1(BufferedWriter writer) throws IOException {
        String tmpClause = "";
        int oij = 0;
        int tij = 0;

        for (int i = 1; i <= this.size; i++) {
            for (int j = 1; j <= this.size; j++) {
                oij = -(this.size * this.size + (i - 1) * this.size + j);
                tij = -((i - 1) * this.size + j);
                tmpClause = oij + " " + tij + " 0\n";
                writer.append(tmpClause);
            }
        }
    }


    public void createPhi2(BufferedWriter writer) throws IOException {
        String tmpClause1 = "";
        String tmpClause2 = "";
        String tmpClause3 = "";
        String tmpClause4 = "";
        String tmpClause5 = "";
        String tmpClause6 = "";
        String tmpClause7 = "";
        String tmpClause8 = "";
        String tmpClause9 = "";
        String tmpClause10 = "";
        String tmpClause11 = "";
        String tmpClause12 = "";
        String tmpClause13 = "";
        String tmpClause14 = "";
        String tmpClause15 = "";
        int tij = 0;
        int oiP1j = 0;  //O_[i+1,j]
        int oiM1j = 0;  //O_[i-1,j]
        int oijP1 = 0;  //O_[i,j+1]
        int oijM1 = 0;  //O_[i.j-1]
        int kiP1jij = 0; //K_[i+1,j,i,j] -- Tree in [i,j] connects to Tent [i+1,j]
        int kiM1jij = 0; //K_[i-1,j,i,j] -- Tree in [i,j] connects to Tent [i-1,j]
        int kijP1ij = 0; //K_[i,j+1,i,j] -- Tree in [i,j] connects to Tent [i,j+1]
        int kijM1ij = 0; //K_[i,j-1,i,j] -- Tree in [i,j] connects to Tent [i,j-1]

        for (int i = 2; i <= this.size-1; i++) {
            for (int j = 2; j <= this.size-1; j++) {
                tij =  (i - 1) * this.size + j;
                oiP1j =  this.size * this.size + i * this.size + j;
                oiM1j =  this.size * this.size + (i - 2) * this.size + j;
                oijP1 =  this.size * this.size + (i - 1) * this.size + j + 1;
                oijM1 =  this.size * this.size + (i - 1) * this.size + j - 1;
                kiP1jij = 2 * this.size * this.size + (i - 1) * this.size + j;
                kiM1jij = 3 * this.size * this.size + (i - 1) * this.size + j;
                kijP1ij = 4 * this.size * this.size + (i - 1) * this.size + j;
                kijM1ij = 5 * this.size * this.size + (i - 1) * this.size + j;
                tmpClause1 = -kiP1jij + " " + -kiM1jij + " 0\n";
                tmpClause2 = -kiP1jij + " " + -kijP1ij + " 0\n";
                tmpClause3 = -kiP1jij + " " + -kijM1ij + " 0\n";
                tmpClause4 = -kiM1jij + " " + -kijP1ij + " 0\n";
                tmpClause5 = -kiM1jij + " " + -kijM1ij + " 0\n";
                tmpClause6 = -kijP1ij + " " + -kijM1ij + " 0\n";
                tmpClause7 = -tij + " " + kiP1jij + " " + kiM1jij + " " + kijP1ij + " " + kijM1ij + " 0\n";
                tmpClause8 = -kiP1jij + " " + oiP1j + " 0\n";
                tmpClause9 = -kiM1jij + " " + oiM1j + " 0\n";
                tmpClause10 = -kijP1ij + " " + oijP1 + " 0\n";
                tmpClause11 = -kijM1ij + " " + oijM1 + " 0\n";
                tmpClause12 = -kiP1jij + " " + tij + " 0\n";
                tmpClause13 = -kiM1jij + " " + tij + " 0\n";
                tmpClause14 = -kijP1ij + " " + tij + " 0\n";
                tmpClause15 = -kijM1ij + " " + tij + " 0\n";
                writer.append(tmpClause1);
                writer.append(tmpClause2);
                writer.append(tmpClause3);
                writer.append(tmpClause4);
                writer.append(tmpClause5);
                writer.append(tmpClause6);
                writer.append(tmpClause7);
                writer.append(tmpClause8);
                writer.append(tmpClause9);
                writer.append(tmpClause10);
                writer.append(tmpClause11);
                writer.append(tmpClause12);
                writer.append(tmpClause13);
                writer.append(tmpClause14);
                writer.append(tmpClause15);
            }
        }

        for (int j = 2; j <= this.size-1; j++) {
            int i = 1;
            tij = (i - 1) * this.size + j;
            oiP1j = this.size * this.size + i * this.size + j;
            oijP1 = this.size * this.size + (i - 1) * this.size + j + 1;
            oijM1 = this.size * this.size + (i - 1) * this.size + j - 1;
            kiP1jij = 2 * this.size * this.size + (i - 1) * this.size + j;
            kijP1ij = 4 * this.size * this.size + (i - 1) * this.size + j;
            kijM1ij = 5 * this.size * this.size + (i - 1) * this.size + j;
            tmpClause2 = -kiP1jij + " " + -kijP1ij + " 0\n";
            tmpClause3 = -kiP1jij + " " + -kijM1ij + " 0\n";
            tmpClause6 = -kijP1ij + " " + -kijM1ij + " 0\n";
            tmpClause7 = -tij + " " + kiP1jij + " " + kijP1ij + " " + kijM1ij + " 0\n";
            tmpClause8 = -kiP1jij + " " + oiP1j + " 0\n";
            tmpClause10 = -kijP1ij + " " + oijP1 + " 0\n";
            tmpClause11 = -kijM1ij + " " + oijM1 + " 0\n";
            tmpClause12 = -kiP1jij + " " + tij + " 0\n";
            tmpClause14 = -kijP1ij + " " + tij + " 0\n";
            tmpClause15 = -kijM1ij + " " + tij + " 0\n";
            writer.append(tmpClause2);
            writer.append(tmpClause3);
            writer.append(tmpClause6);
            writer.append(tmpClause7);
            writer.append(tmpClause8);
            writer.append(tmpClause10);
            writer.append(tmpClause11);
            writer.append(tmpClause12);
            writer.append(tmpClause14);
            writer.append(tmpClause15);


            i = this.size;
            tij =  (i - 1) * this.size + j;
            oiM1j =  this.size * this.size + (i - 2) * this.size + j;
            oijP1 =  this.size * this.size + (i - 1) * this.size + j + 1;
            oijM1 =  this.size * this.size + (i - 1) * this.size + j - 1;
            kiM1jij = 3 * this.size * this.size + (i - 1) * this.size + j;
            kijP1ij = 4 * this.size * this.size + (i - 1) * this.size + j;
            kijM1ij = 5 * this.size * this.size + (i - 1) * this.size + j;
            tmpClause4 = -kiM1jij + " " + -kijP1ij + " 0\n";
            tmpClause5 = -kiM1jij + " " + -kijM1ij + " 0\n";
            tmpClause6 = -kijP1ij + " " + -kijM1ij + " 0\n";
            tmpClause7 = -tij + " " + kiM1jij + " " + kijP1ij + " " + kijM1ij + " 0\n";
            tmpClause9 = -kiM1jij + " " + oiM1j + " 0\n";
            tmpClause10 = -kijP1ij + " " + oijP1 + " 0\n";
            tmpClause11 = -kijM1ij + " " + oijM1 + " 0\n";
            tmpClause13 = -kiM1jij + " " + tij + " 0\n";
            tmpClause14 = -kijP1ij + " " + tij + " 0\n";
            tmpClause15 = -kijM1ij + " " + tij + " 0\n";
            writer.append(tmpClause4);
            writer.append(tmpClause5);
            writer.append(tmpClause6);
            writer.append(tmpClause7);
            writer.append(tmpClause9);
            writer.append(tmpClause10);
            writer.append(tmpClause11);
            writer.append(tmpClause13);
            writer.append(tmpClause14);
            writer.append(tmpClause15);
        }


        for (int i = 2; i <= this.size-1; i++) {
            int j = 1;
            tij = (i - 1) * this.size + j;
            oiP1j = this.size * this.size + i * this.size + j;
            oiM1j = this.size * this.size + (i - 2) * this.size + j;
            oijP1 = this.size * this.size + (i - 1) * this.size + j + 1;
            kiP1jij = 2 * this.size * this.size + (i - 1) * this.size + j;
            kiM1jij = 3 * this.size * this.size + (i - 1) * this.size + j;
            kijP1ij = 4 * this.size * this.size + (i - 1) * this.size + j;
            tmpClause1 = -kiP1jij + " " + -kiM1jij + " 0\n";
            tmpClause2 = -kiP1jij + " " + -kijP1ij + " 0\n";
            tmpClause4 = -kiM1jij + " " + -kijP1ij + " 0\n";
            tmpClause7 = -tij + " " + kiP1jij + " " + kiM1jij + " " + kijP1ij + " 0\n";
            tmpClause8 = -kiP1jij + " " + oiP1j + " 0\n";
            tmpClause9 = -kiM1jij + " " + oiM1j + " 0\n";
            tmpClause10 = -kijP1ij + " " + oijP1 + " 0\n";
            tmpClause12 = -kiP1jij + " " + tij + " 0\n";
            tmpClause13 = -kiM1jij + " " + tij + " 0\n";
            tmpClause14 = -kijP1ij + " " + tij + " 0\n";
            writer.append(tmpClause1);
            writer.append(tmpClause2);
            writer.append(tmpClause4);
            writer.append(tmpClause7);
            writer.append(tmpClause8);
            writer.append(tmpClause9);
            writer.append(tmpClause10);
            writer.append(tmpClause12);
            writer.append(tmpClause13);
            writer.append(tmpClause14);


            j = this.size;
            tij =  (i - 1) * this.size + j;
            oiP1j =  this.size * this.size + i * this.size + j;
            oiM1j =  this.size * this.size + (i - 2) * this.size + j;
            oijM1 =  this.size * this.size + (i - 1) * this.size + j - 1;
            kiP1jij = 2 * this.size * this.size + (i - 1) * this.size + j;
            kiM1jij = 3 * this.size * this.size + (i - 1) * this.size + j;
            kijM1ij = 5 * this.size * this.size + (i - 1) * this.size + j;
            tmpClause1 = -kiP1jij + " " + -kiM1jij + " 0\n";
            tmpClause3 = -kiP1jij + " " + -kijM1ij + " 0\n";
            tmpClause5 = -kiM1jij + " " + -kijM1ij + " 0\n";
            tmpClause7 = -tij + " " + kiP1jij + " " + kiM1jij + " " + kijM1ij + " 0\n";
            tmpClause8 = -kiP1jij + " " + oiP1j + " 0\n";
            tmpClause9 = -kiM1jij + " " + oiM1j + " 0\n";
            tmpClause11 = -kijM1ij + " " + oijM1 + " 0\n";
            tmpClause12 = -kiP1jij + " " + tij + " 0\n";
            tmpClause13 = -kiM1jij + " " + tij + " 0\n";
            tmpClause15 = -kijM1ij + " " + tij + " 0\n";
            writer.append(tmpClause1);
            writer.append(tmpClause3);
            writer.append(tmpClause5);
            writer.append(tmpClause7);
            writer.append(tmpClause8);
            writer.append(tmpClause9);
            writer.append(tmpClause11);
            writer.append(tmpClause12);
            writer.append(tmpClause13);
            writer.append(tmpClause15);
        }

        // Now we go for the edges (ARBA PINOT)
        // Top-Left Corner
        tij =  (1 - 1) * this.size + 1;
        oiP1j =  this.size * this.size + 1 * this.size + 1;
        oijP1 =  this.size * this.size + (1 - 1) * this.size + 1 + 1;
        kiP1jij = 2 * this.size * this.size + (1 - 1) * this.size + 1;
        kijP1ij = 4 * this.size * this.size + (1 - 1) * this.size + 1;
        tmpClause2 = -kiP1jij + " " + -kijP1ij + " 0\n";
        tmpClause7 = -tij + " " + kiP1jij + " " + kijP1ij + " 0\n";
        tmpClause8 = -kiP1jij + " " + oiP1j + " 0\n";
        tmpClause10 = -kijP1ij + " " + oijP1 + " 0\n";
        tmpClause12 = -kiP1jij + " " + tij + " 0\n";
        tmpClause14 = -kijP1ij + " " + tij + " 0\n";
        writer.append(tmpClause2);
        writer.append(tmpClause7);
        writer.append(tmpClause8);
        writer.append(tmpClause10);
        writer.append(tmpClause12);
        writer.append(tmpClause14);

        // Bottom-Left Corner
        tij =  (this.size - 1) * this.size + 1;
        oiM1j =  this.size * this.size + (this.size - 2) * this.size + 1;
        oijP1 =  this.size * this.size + (this.size - 1) * this.size + 1 + 1;
        kiM1jij = 3 * this.size * this.size + (this.size - 1) * this.size + 1;
        kijP1ij = 4 * this.size * this.size + (this.size - 1) * this.size + 1;
        tmpClause4 = -kiM1jij + " " + -kijP1ij + " 0\n";
        tmpClause7 = -tij + " "  + kiM1jij + " " + kijP1ij + " 0\n";
        tmpClause9 = -kiM1jij + " " + oiM1j + " 0\n";
        tmpClause10 = -kijP1ij + " " + oijP1 + " 0\n";
        tmpClause13 = -kiM1jij + " " + tij + " 0\n";
        tmpClause14 = -kijP1ij + " " + tij + " 0\n";
        writer.append(tmpClause4);
        writer.append(tmpClause7);
        writer.append(tmpClause9);
        writer.append(tmpClause10);
        writer.append(tmpClause13);
        writer.append(tmpClause14);


        // Top-Right Corner
        tij =  (1 - 1) * this.size + this.size;
        oiP1j =  this.size * this.size + 1 * this.size + this.size;
        oijM1 =  this.size * this.size + (1 - 1) * this.size + this.size - 1;
        kiP1jij = 2 * this.size * this.size + (1 - 1) * this.size + this.size;
        kijM1ij = 5 * this.size * this.size + (1 - 1) * this.size + this.size;
        tmpClause3 = -kiP1jij + " " + -kijM1ij + " 0\n";
        tmpClause7 = -tij + " " + kiP1jij + " "  + kijM1ij + " 0\n";
        tmpClause8 = -kiP1jij + " " + oiP1j + " 0\n";
        tmpClause11 = -kijM1ij + " " + oijM1 + " 0\n";
        tmpClause12 = -kiP1jij + " " + tij + " 0\n";
        tmpClause15 = -kijM1ij + " " + tij + " 0\n";
        writer.append(tmpClause3);
        writer.append(tmpClause7);
        writer.append(tmpClause8);
        writer.append(tmpClause11);
        writer.append(tmpClause12);
        writer.append(tmpClause15);

        // Bottom-Right Corner
        tij =  (this.size - 1) * this.size + this.size;
        oiM1j =  this.size * this.size + (this.size - 2) * this.size + this.size;
        oijM1 =  this.size * this.size + (this.size - 1) * this.size + this.size - 1;
        kiM1jij = 3 * this.size * this.size + (this.size - 1) * this.size + this.size;
        kijM1ij = 5 * this.size * this.size + (this.size - 1) * this.size + this.size;
        tmpClause5 = -kiM1jij + " " + -kijM1ij + " 0\n";
        tmpClause7 = -tij + " " + kiM1jij + " " + kijM1ij + " 0\n";
        tmpClause9 = -kiM1jij + " " + oiM1j + " 0\n";
        tmpClause11 = -kijM1ij + " " + oijM1 + " 0\n";
        tmpClause13 = -kiM1jij + " " + tij + " 0\n";
        tmpClause15 = -kijM1ij + " " + tij + " 0\n";
        writer.append(tmpClause5);
        writer.append(tmpClause7);
        writer.append(tmpClause9);
        writer.append(tmpClause11);
        writer.append(tmpClause13);
        writer.append(tmpClause15);
    }

    public void createPhi3(BufferedWriter writer) throws IOException {
        String tmpClause = "";
        int oij = 0;
        int oiljm = 0;  //O_(i+l,j+m)

        for (int i = 1; i <= this.size; i++) {
            for (int j = 1; j <= this.size; j++) {
                for (int l = -1; l <= 1; l++){
                    for(int m = -1; m <= 1; m++){
                        // We do not want to compare O_(i,j) to itself, so we make sure that l = m = 0 does not happen
                        if ( (! ( l == m && l == 0)) && inMap(i+l, j+m)) {
                            oij = -( this.size * this.size + (i - 1) * this.size + j);
                            oiljm = -( this.size * this.size + (i + l - 1) * this.size + j + m);
                            tmpClause = oij + " " + oiljm + " 0\n";
                            writer.append(tmpClause);
                        }
                    }
                }

            }
        }
    }

    public void createPhi4(BufferedWriter writer) throws IOException {
        String tmpClause = "";
        String tmpClauseLeast = "";
        String limhok1="";
        String limhok2="";
        int oij = 0;
        int mgij = 0;
        int xik = 0;
        int ngij = 0;
        writer.append("c BEGIN PHI4\n");
        int upperLog = ourLogSquare();
        for (int i = 1; i <= this.size; i++) {
            for (int j = 1; j <= this.size; j++) {
                oij = this.size * this.size + (i - 1) * this.size + j;
                for (int k = 0; k <= this.size -1; k++) {
                    tmpClause = -oij +"";
                    limhok1 = "c ¬O"+i+","+j+" ";
                    for (int g = 1; g <= k; g++) {
                        mgij = 2 * this.size * this.size * this.size + 8 *this.size * this.size + (g - 1)*this.size * this.size + (i-1) * this.size + j;
                        tmpClause = tmpClause + " " + mgij;
                        limhok1=limhok1+ " OR  M"+g+","+i+","+j;
                    }
                    xik = 6 * this.size * this.size + (i-1)*this.size + k + 1;
                    tmpClause = tmpClause +" " + -xik +" 0\n";
                    limhok1 = limhok1+" OR ¬X"+i+","+k;
                    //writer.append("c ¬O"+i+","+j+" V M1"+","+i+","+j+" V ... V M"+k+","+i+","+j+" V ¬x"+i+","+k+" is therefore:\n");
                    writer.append(limhok1+"\n");
                    writer.append(tmpClause);
                    writer.append("c The string s"+i+","+j+" is: "+createSij((i-1)*this.size + j )+"\n");

                    for (int g = 1 ; g <= k ; g++){
                        mgij = 2 * this.size * this.size * this.size + 8 *this.size * this.size + (g - 1)*this.size * this.size + (i-1) * this.size + j;
                        for (int l = 1 ; l <= upperLog ; l++){
                            tmpClause = -mgij + " "+alpha(i,j,g,l)+" "+ -xik+" 0\n";// + " "+ -oij +" 0\n";
                            writer.append("c ¬M"+g+","+i+","+j+" V a("+i+","+j+","+g+","+l+") V ¬x"+i+","+k+"¬O"+i+","+j+" are hence:\n");
                            writer.append(tmpClause);
                        }
                    }

                    //writer.append("c MIDDLE PHI4\n");


                    if(k!=0) {
                        tmpClauseLeast = oij + "";
                        limhok2 = "c O" + i + "," + j + " ";
                        for (int g = 1; g <= this.size - k; g++) {
                            ngij = 3 * this.size * this.size * this.size + 8 * this.size * this.size + (g - 1) * this.size * this.size + (i - 1) * this.size + j;
                            //mgij = 2 * this.size * this.size * this.size + 8 *this.size * this.size + (g - 1)*this.size * this.size + (i-1) * this.size + j;
                            tmpClauseLeast = tmpClauseLeast + " " + ngij;
                            limhok2 = limhok2 + " OR  N" + g + "," + i + "," + j;
                        }
                        xik = 6 * this.size * this.size + (i - 1) * this.size + k + 1;
                        limhok2 = limhok2 + " OR ¬X" + i + "," + k;
                        writer.append(limhok2 + "\n");
                        tmpClauseLeast = tmpClauseLeast + " " + -xik + " 0\n";
                        writer.append(tmpClauseLeast);
                        writer.append("c The string s" + i + "," + j + " is: " + createSij((i - 1) * this.size + j) + "\n");

                        for (int g = 1; g <= this.size - k; g++) {
                            ngij = 3 * this.size * this.size * this.size + 8 * this.size * this.size + (g - 1) * this.size * this.size + (i - 1) * this.size + j;
                            //mgij = 2 * this.size * this.size * this.size + 8 *this.size * this.size + (g - 1)*this.size * this.size + (i-1) * this.size + j;
                            for (int l = 1; l <= upperLog; l++) {
                                tmpClauseLeast = -ngij + " " + beta(i, j, g, l) + " " + -xik + " 0\n";//+ " " + oij + " 0\n";
                                writer.append("c ¬N" + g + "," + i + "," + j + " V b(" + i + "," + j + "," + g + "," + l + ") V ¬x" + i + "," + k + "¬O" + i + "," + j + " are hence:\n");
                                writer.append(tmpClauseLeast);
                            }
                        }
                    }
                }
            }
        }



        /*for (int i = 1; i <= this.size; i++) {
            for (int j = 1; j <= this.size; j++) {
                oij = this.size * this.size + (i - 1) * this.size + j;

                for (int k = 1; k <= this.size -1; k++) {
                    tmpClause = oij +"";
                    for (int g = 1; g <= this.size - k; g++) {
                        ngij = 3 * this.size * this.size * this.size + 8 *this.size * this.size + (g - 1)*this.size * this.size + (i-1) * this.size + j;
                        tmpClause = tmpClause + " " + ngij;
                    }
                    xik = 6 * this.size * this.size + (i-1)*this.size + this.size - k + 1;
                    tmpClause = tmpClause +" " + -xik +" 0\n";
                    writer.append(tmpClause);

                    for (int g = 1 ; g <= this.size - k; g++){
                        ngij = 3 * this.size * this.size * this.size + 8 *this.size * this.size + (g - 1)*this.size * this.size + (i-1) * this.size + j;
                        for (int l = 1 ; l <= upperLog ; l++){
                            tmpClause = -ngij + " "+beta(i,j,g,l)+" "+ -xik+" 0\n";
                            writer.append(tmpClause);
                        }
                    }
                }
            }
        }*/
        writer.append("c END PHI4\n");

    }

    public void createPhi5(BufferedWriter writer) throws IOException {
        /*String tmpClause = "";
        String tmpClauseLeast = "";
        int oij = 0;
        int rgij = 0;
        int yjk = 0;
        int sgij = 0;
        int upperLog = ourLogSquare();
        for (int i = 1; i <= this.size; i++) {
            for (int j = 1; j <= this.size; j++) {
                oij = this.size * this.size + (i - 1) * this.size + j;
                for (int k = 0; k <= this.size - 1; k++) {
                    tmpClause = -oij + "";
                    for (int g = 1; g <= k; g++) {
                        rgij = 8 * this.size * this.size + (g - 1) * this.size * this.size + (i - 1) * this.size + j;
                        tmpClause = tmpClause + " " + rgij;
                    }
                    yjk = 7 * this.size * this.size + (j - 1) * this.size + k + 1;
                    tmpClause = tmpClause + " " + -yjk + " 0\n";
                    writer.append("c ¬O" + i + "," + j + " V R1" + "," + i + "," + j + " V ... V R" + k + "," + i + "," + j + " V ¬y" + j + "," + k + " is therefore:\n");
                    writer.append(tmpClause);
                    writer.append("c The string s" + i + "," + j + " is:" + createSij((i - 1) * this.size + j) + "\n");
                    for (int g = 1; g <= k; g++) {
                        rgij = 8 * this.size * this.size + (g - 1) * this.size * this.size + (i - 1) * this.size + j;
                        for (int l = 1; l <= upperLog; l++) {
                            tmpClause = -rgij + " " + gamma(i, j, g, l) + " " + -yjk + " 0\n";
                            writer.append("c ¬R" + g + "," + i + "," + j + " V ג(" + i + "," + j + "," + g + "," + l + ") V ¬y" + j + "," + k + " are hence:\n");
                            writer.append(tmpClause);
                        }
                    }

                    //MIDDLE PHI5

                    if(k!=0) {
                        tmpClauseLeast = oij + "";
                        for (int g = 1; g <= this.size - k; g++) {
                            sgij = this.size * this.size * this.size + 8 * this.size * this.size + (g - 1) * this.size * this.size + (i - 1) * this.size + j;
                            tmpClauseLeast = tmpClauseLeast + " " + sgij;
                        }
                        yjk = 7 * this.size * this.size + (i - 1) * this.size + k + 1;
                        tmpClauseLeast = tmpClauseLeast + " " + -yjk + " 0\n";
                        writer.append(tmpClauseLeast);

                        for (int g = 1; g <= this.size - k; g++) {
                            sgij = this.size * this.size * this.size + 8 * this.size * this.size + (g - 1) * this.size * this.size + (i - 1) * this.size + j;
                            for (int l = 1; l <= upperLog; l++) {
                                tmpClauseLeast = -sgij + " " + delta(i, j, g, l) + " " + -yjk + " 0\n";
                                writer.append(tmpClauseLeast);
                            }
                        }
                    }
                }
            }
        }*/

        String tmpClause = "";
        String tmpClauseLeast = "";
        String limhok1="";
        String limhok2="";
        int oij = 0;
        int rgij = 0;
        int yjk = 0;
        int sgij = 0;
        writer.append("c BEGIN PHI5\n");
        int upperLog = ourLogSquare();
        for (int i = 1; i <= this.size; i++) {
            for (int j = 1; j <= this.size; j++) {
                oij = this.size * this.size + (i - 1) * this.size + j;
                for (int k = 0; k <= this.size -1; k++) {
                    tmpClause = -oij +"";
                    limhok1 = "c ¬O"+i+","+j+" ";
                    for (int g = 1; g <= k; g++) {
                        rgij = 8 *this.size * this.size + (g - 1)*this.size * this.size + (i-1) * this.size + j;
                        tmpClause = tmpClause + " " + rgij;
                        limhok1=limhok1+ " OR  R"+g+","+i+","+j;
                    }
                    yjk = 7 * this.size * this.size + (j-1)*this.size + k + 1;
                    tmpClause = tmpClause +" " + -yjk +" 0\n";
                    limhok1 = limhok1+" OR ¬Y"+j+","+k;
                    writer.append(limhok1+"\n");
                    writer.append(tmpClause);
                    writer.append("c The string s"+i+","+j+" is: "+createSij((i-1)*this.size + j )+"\n");

                    for (int g = 1 ; g <= k ; g++){
                        rgij =  8 *this.size * this.size + (g - 1)*this.size * this.size + (i-1) * this.size + j;
                        for (int l = 1 ; l <= upperLog ; l++){
                            tmpClause = -rgij + " "+gamma(i,j,g,l)+" "+ -yjk+" 0\n";// + " "+ -oij +" 0\n";
                            writer.append("c ¬R"+g+","+i+","+j+" V gam("+i+","+j+","+g+","+l+") V ¬y"+j+","+k+"¬O"+i+","+j+" is:\n");
                            writer.append(tmpClause);
                        }
                    }

                    //writer.append("c MIDDLE PHI5\n");


                    if(k!=0) {
                        tmpClauseLeast = oij + "";
                        limhok2 = "c O" + i + "," + j + " ";
                        for (int g = 1; g <= this.size - k; g++) {
                            sgij = this.size * this.size * this.size + 8 * this.size * this.size + (g - 1) * this.size * this.size + (i - 1) * this.size + j;
                            tmpClauseLeast = tmpClauseLeast + " " + sgij;
                            limhok2 = limhok2 + " OR  S" + g + "," + i + "," + j;
                        }
                        yjk = 7 * this.size * this.size + (j - 1) * this.size + k + 1;
                        limhok2 = limhok2 + " OR ¬Y" + j + "," + k;
                        writer.append(limhok2 + "\n");
                        tmpClauseLeast = tmpClauseLeast + " " + -yjk + " 0\n";
                        writer.append(tmpClauseLeast);
                        writer.append("c The string s" + i + "," + j + " is: " + createSij((i - 1) * this.size + j) + "\n");

                        for (int g = 1; g <= this.size - k; g++) {
                            sgij = this.size * this.size * this.size + 8 * this.size * this.size + (g - 1) * this.size * this.size + (i - 1) * this.size + j;
                            for (int l = 1; l <= upperLog; l++) {
                                tmpClauseLeast = -sgij + " " + delta(i, j, g, l) + " " + -yjk + " 0\n";//+ " " + oij + " 0\n";
                                writer.append("c ¬S" + g + "," + i + "," + j + " V del(" + i + "," + j + "," + g + "," + l + ") V ¬Y" + j + "," + k + "¬O" + i + "," + j + " are hence:\n");
                                writer.append(tmpClauseLeast);
                            }
                        }
                    }
                }
            }
        }

        /*for (int i = 1; i <= this.size; i++) {
            for (int j = 1; j <= this.size; j++) {
                oij = this.size * this.size + (i - 1) * this.size + j;

                for (int k = 1; k <= this.size -1; k++) {
                    tmpClause = oij +"";
                    for (int g = 1; g <= k; g++) {
                        sgij = this.size * this.size * this.size + 8 *this.size * this.size + (g-1)*this.size * this.size + (i-1) * this.size + j;
                        tmpClause = tmpClause + " " + sgij;
                    }
                    yjk = 6 * this.size * this.size + (i-1)*this.size + k + 1;
                    tmpClause = tmpClause +" " + -yjk +" 0\n";
                    writer.append(tmpClause);

                    for (int g = 1 ; g <= k ; g++){
                        sgij = this.size * this.size * this.size + 8 *this.size * this.size + (g-1)*this.size * this.size + (i-1) * this.size + j;
                        for (int l = 1 ; l <= upperLog ; l++){
                            tmpClause = -sgij + " "+delta(i,j,g,l)+" "+ -yjk+" 0\n";
                            writer.append(tmpClause);
                        }
                    }
                }
            }
        }*/

    }

    /*public void createPhi6(BufferedWriter writer) throws IOException {
        String tmpClause = "";
        int xik = 0;
        int xik1 = 0;
        int xik2 = 0;
        int yjk = 0;
        int yjk1 = 0;
        int yjk2 = 0;

        for (int i = 1; i <= this.size; i++) {
            xik = 6 * this.size * this.size + (i-1)*this.size + 1; //This is actually xi0 (for k=0)
            tmpClause = xik + ""; // We add empty string so it becomes a string
            for (int k = 1; k <= this.size - 1; k++) {
                xik = 6 * this.size * this.size + (i-1)*this.size + k + 1;
                tmpClause = tmpClause + " " + xik;
            }
            tmpClause = tmpClause +" 0\n";
            writer.append(tmpClause);

            for (int k1 = 0; k1 <= this.size - 1; k1++){
                for (int k2 = 0; k2 <= this.size - 1; k2++){
                    if (k1 != k2){
                        xik1 = 6 * this.size * this.size + (i-1)*this.size + k1 + 1;
                        xik2 = 6 * this.size * this.size + (i-1)*this.size + k2 + 1;
                        tmpClause = -xik1 + " " + -xik2 + " 0\n";
                        writer.append(tmpClause);
                    }
                }
            }
        }



        for (int j = 1; j <= this.size; j++) {
            yjk = 7 * this.size * this.size + (j-1)*this.size + 1; //This is actually yi0 (for k=0)
            tmpClause = yjk + ""; // We add empty string so it becomes a string
            for (int k = 1; k <= this.size - 1; k++) {
                yjk = 7 * this.size * this.size + (j-1)*this.size + k + 1;
                tmpClause = tmpClause + " " + yjk;
            }
            tmpClause = tmpClause +" 0\n";
            writer.append(tmpClause);

            for (int k1 = 0; k1 <= this.size - 1; k1++){
                for (int k2 = 0; k2 <= this.size - 1; k2++){
                    if (k1 != k2){
                        yjk1 = 7 * this.size * this.size + (j-1)*this.size + k1 + 1;
                        yjk2 = 7 * this.size * this.size + (j-1)*this.size + k2 + 1;
                        tmpClause = -yjk1 + " " + -yjk2 + " 0\n";
                        writer.append(tmpClause);
                    }
                }
            }
        }
    }*/


    public void createPhi6(BufferedWriter writer) throws IOException {
        String tmpClause = "";
        String tmpClause1 = "";
        String tmpClause2 = "";
        String tmpClause3 = "";
        String tmpClause4 = "";
        String tmpClause5 = "";
        String tmpClause6 = "";
        int oij = 0;  //O_[i,j]
        int kijiP1j = 0; //K_[i,j,i+1,j] -- Tree in [i+1,j] connects to Tent [i,j]
        int kijiM1j = 0; //K_[i,j,i-1,j] -- Tree in [i-1,j] connects to Tent [i,j]
        int kijijP1 = 0; //K_[i,j,i,j+1] -- Tree in [i,j+1] connects to Tent [i,j]
        int kijijM1 = 0; //K_[i,j,i,j-1] -- Tree in [i,j-1] connects to Tent [i,j]

        for (int i = 2; i <= this.size-1; i++) {
            for (int j = 2; j <= this.size-1; j++) {
                oij =  this.size * this.size + (i -1) * this.size + j;
                kijiP1j = 3 * this.size * this.size +i * this.size + j;
                kijiM1j = 2 * this.size * this.size + (i - 2) * this.size + j;
                kijijP1 = 5 * this.size * this.size + (i - 1) * this.size + j+1;
                kijijM1 = 4 * this.size * this.size + (i - 1) * this.size + j-1;
                tmpClause = -oij + " " + kijiP1j + " " +kijiM1j + " " +kijijP1 + " " +kijijM1 + " 0\n";
                writer.append(tmpClause);
                tmpClause1 = -oij + " " + -kijiP1j + " " + -kijiM1j + " 0\n";
                writer.append(tmpClause1);
                tmpClause2 = -oij + " " + -kijiP1j + " " + -kijijP1 + " 0\n";
                writer.append(tmpClause2);
                tmpClause3 = -oij + " " + -kijiP1j + " " + -kijijM1 + " 0\n";
                writer.append(tmpClause3);
                tmpClause4 = -oij + " " + -kijiM1j + " " + -kijijP1 + " 0\n";
                writer.append(tmpClause4);
                tmpClause5 = -oij + " " + -kijiM1j + " " + -kijijM1 + " 0\n";
                writer.append(tmpClause5);
                tmpClause6 = -oij + " " + -kijijP1 + " " + -kijijM1 + " 0\n";
                writer.append(tmpClause6);
            }
        }

        // First line, assume: i = 1
        for (int j = 2; j <= this.size-1; j++) {
            int i = 1;
            oij =  this.size * this.size + (i -1) * this.size + j;
            kijiP1j = 3 * this.size * this.size +i * this.size + j;
            //kijiM1j = 2 * this.size * this.size + (i - 2) * this.size + j;
            kijijP1 = 5 * this.size * this.size + (i - 1) * this.size + j+1;
            kijijM1 = 4 * this.size * this.size + (i - 1) * this.size + j-1;
            tmpClause = -oij + " " + kijiP1j + " " +kijijP1 + " " +kijijM1 + " 0\n";
            writer.append(tmpClause);
            //tmpClause1 = -oij + " " + -kijiP1j + " " + -kijiM1j + " 0\n";
            //writer.append(tmpClause1);
            tmpClause2 = -oij + " " + -kijiP1j + " " + -kijijP1 + " 0\n";
            writer.append(tmpClause2);
            tmpClause3 = -oij + " " + -kijiP1j + " " + -kijijM1 + " 0\n";
            writer.append(tmpClause3);
            //tmpClause4 = -oij + " " + -kijiM1j + " " + -kijijP1 + " 0\n";
            //writer.append(tmpClause4);
            //tmpClause5 = -oij + " " + -kijiM1j + " " + -kijijM1 + " 0\n";
            //writer.append(tmpClause5);
            tmpClause6 = -oij + " " + -kijijP1 + " " + -kijijM1 + " 0\n";
            writer.append(tmpClause6);
        }


        // Last line, assume: i = n-1
        for (int j = 2; j <= this.size-1; j++) {
            int i = this.size;
            oij =  this.size * this.size + (i -1) * this.size + j;
            //kijiP1j = 3 * this.size * this.size +i * this.size + j;
            kijiM1j = 2 * this.size * this.size + (i - 2) * this.size + j;
            kijijP1 = 5 * this.size * this.size + (i - 1) * this.size + j+1;
            kijijM1 = 4 * this.size * this.size + (i - 1) * this.size + j-1;
            tmpClause = -oij + " " + kijiM1j + " " +kijijP1 + " " +kijijM1 + " 0\n";
            writer.append(tmpClause);
            //tmpClause1 = -oij + " " + -kijiP1j + " " + -kijiM1j + " 0\n";
            //writer.append(tmpClause1);
            //tmpClause2 = -oij + " " + -kijiP1j + " " + -kijijP1 + " 0\n";
            //writer.append(tmpClause2);
            //tmpClause3 = -oij + " " + -kijiP1j + " " + -kijijM1 + " 0\n";
            //writer.append(tmpClause3);
            tmpClause4 = -oij + " " + -kijiM1j + " " + -kijijP1 + " 0\n";
            writer.append(tmpClause4);
            tmpClause5 = -oij + " " + -kijiM1j + " " + -kijijM1 + " 0\n";
            writer.append(tmpClause5);
            tmpClause6 = -oij + " " + -kijijP1 + " " + -kijijM1 + " 0\n";
            writer.append(tmpClause6);
        }


        // Leftist column, assume: j = 1
        for (int i = 2; i <= this.size-1; i++) {
            int j = 1;
            oij =  this.size * this.size + (i -1) * this.size + j;
            kijiP1j = 3 * this.size * this.size +i * this.size + j;
            kijiM1j = 2 * this.size * this.size + (i - 2) * this.size + j;
            kijijP1 = 5 * this.size * this.size + (i - 1) * this.size + j+1;
            //kijijM1 = 4 * this.size * this.size + (i - 1) * this.size + j-1;
            tmpClause = -oij + " " + kijiP1j + " " + kijiM1j + " " +kijijP1 + " 0\n";
            writer.append(tmpClause);
            tmpClause1 = -oij + " " + -kijiP1j + " " + -kijiM1j + " 0\n";
            writer.append(tmpClause1);
            tmpClause2 = -oij + " " + -kijiP1j + " " + -kijijP1 + " 0\n";
            writer.append(tmpClause2);
            //tmpClause3 = -oij + " " + -kijiP1j + " " + -kijijM1 + " 0\n";
            //writer.append(tmpClause3);
            tmpClause4 = -oij + " " + -kijiM1j + " " + -kijijP1 + " 0\n";
            writer.append(tmpClause4);
            //tmpClause5 = -oij + " " + -kijiM1j + " " + -kijijM1 + " 0\n";
            //writer.append(tmpClause5);
            //tmpClause6 = -oij + " " + -kijijP1 + " " + -kijijM1 + " 0\n";
            //writer.append(tmpClause6);
        }


        // Very right super column, assume: j = n - 1
        for (int i = 2; i <= this.size-1; i++) {
            int j = this.size;
            oij =  this.size * this.size + (i -1) * this.size + j;
            kijiP1j = 3 * this.size * this.size +i * this.size + j;
            kijiM1j = 2 * this.size * this.size + (i - 2) * this.size + j;
            //kijijP1 = 5 * this.size * this.size + (i - 1) * this.size + j+1;
            kijijM1 = 4 * this.size * this.size + (i - 1) * this.size + j-1;
            tmpClause = -oij + " " + kijiP1j + " " + kijiM1j + " " +kijijM1 + " 0\n";
            writer.append(tmpClause);
            tmpClause1 = -oij + " " + -kijiP1j + " " + -kijiM1j + " 0\n";
            writer.append(tmpClause1);
            //tmpClause2 = -oij + " " + -kijiP1j + " " + -kijijP1 + " 0\n";
            //writer.append(tmpClause2);
            tmpClause3 = -oij + " " + -kijiP1j + " " + -kijijM1 + " 0\n";
            writer.append(tmpClause3);
            //tmpClause4 = -oij + " " + -kijiM1j + " " + -kijijP1 + " 0\n";
            //writer.append(tmpClause4);
            tmpClause5 = -oij + " " + -kijiM1j + " " + -kijijM1 + " 0\n";
            writer.append(tmpClause5);
            //tmpClause6 = -oij + " " + -kijijP1 + " " + -kijijM1 + " 0\n";
            //writer.append(tmpClause6);
        }

        //////////////////////
        // For the 4 corners//
        //////////////////////

        writer.append("c FROM HERE\n");
        // Top-Left Corner
        int i = 1;
        int j = 1;
        oij =  this.size * this.size + (i -1) * this.size + j;
        kijiP1j = 3 * this.size * this.size +i * this.size + j;
        //kijiM1j = 2 * this.size * this.size + (i - 2) * this.size + j;
        kijijP1 = 5 * this.size * this.size + (i - 1) * this.size + j+1;
        //kijijM1 = 4 * this.size * this.size + (i - 1) * this.size + j-1;
        tmpClause = -oij + " " + kijiP1j + " " + kijijP1 + " 0\n";
        writer.append(tmpClause);
        //tmpClause1 = -oij + " " + -kijiP1j + " " + -kijiM1j + " 0\n";
        //writer.append(tmpClause1);
        tmpClause2 = -oij + " " + -kijiP1j + " " + -kijijP1 + " 0\n";
        writer.append(tmpClause2);
        //tmpClause3 = -oij + " " + -kijiP1j + " " + -kijijM1 + " 0\n";
        //writer.append(tmpClause3);
        //tmpClause4 = -oij + " " + -kijiM1j + " " + -kijijP1 + " 0\n";
        //writer.append(tmpClause4);
        //tmpClause5 = -oij + " " + -kijiM1j + " " + -kijijM1 + " 0\n";
        //writer.append(tmpClause5);
        //tmpClause6 = -oij + " " + -kijijP1 + " " + -kijijM1 + " 0\n";
        //writer.append(tmpClause6);


        // Bottom-Left Corner
        i = this.size;
        j = 1;
        oij =  this.size * this.size + (i -1) * this.size + j;
        //kijiP1j = 3 * this.size * this.size +i * this.size + j;
        kijiM1j = 2 * this.size * this.size + (i - 2) * this.size + j;
        kijijP1 = 5 * this.size * this.size + (i - 1) * this.size + j+1;
        //kijijM1 = 4 * this.size * this.size + (i - 1) * this.size + j-1;
        tmpClause = -oij + " " + kijiM1j + " " + kijijP1 + " 0\n";
        writer.append(tmpClause);
        //tmpClause1 = -oij + " " + -kijiP1j + " " + -kijiM1j + " 0\n";
        //writer.append(tmpClause1);
        //tmpClause2 = -oij + " " + -kijiP1j + " " + -kijijP1 + " 0\n";
        //writer.append(tmpClause2);
        //tmpClause3 = -oij + " " + -kijiP1j + " " + -kijijM1 + " 0\n";
        writer.append(tmpClause3);
        tmpClause4 = -oij + " " + -kijiM1j + " " + -kijijP1 + " 0\n";
        //writer.append(tmpClause4);
        //tmpClause5 = -oij + " " + -kijiM1j + " " + -kijijM1 + " 0\n";
        //writer.append(tmpClause5);
        //tmpClause6 = -oij + " " + -kijijP1 + " " + -kijijM1 + " 0\n";
        //writer.append(tmpClause6);


        // Bottom-Right Corner
        i = this.size;
        j = this.size;
        oij =  this.size * this.size + (i -1) * this.size + j;
        //kijiP1j = 3 * this.size * this.size +i * this.size + j;
        kijiM1j = 2 * this.size * this.size + (i - 2) * this.size + j;
        //kijijP1 = 5 * this.size * this.size + (i - 1) * this.size + j+1;
        kijijM1 = 4 * this.size * this.size + (i - 1) * this.size + j-1;
        tmpClause = -oij + " " + kijiM1j + " " + kijijM1 + " 0\n";
        writer.append(tmpClause);
        //tmpClause1 = -oij + " " + -kijiP1j + " " + -kijiM1j + " 0\n";
        //writer.append(tmpClause1);
        //tmpClause2 = -oij + " " + -kijiP1j + " " + -kijijP1 + " 0\n";
        //writer.append(tmpClause2);
        //tmpClause3 = -oij + " " + -kijiP1j + " " + -kijijM1 + " 0\n";
        //writer.append(tmpClause3);
        //tmpClause4 = -oij + " " + -kijiM1j + " " + -kijijP1 + " 0\n";
        //writer.append(tmpClause4);
        tmpClause5 = -oij + " " + -kijiM1j + " " + -kijijM1 + " 0\n";
        writer.append(tmpClause5);
        //tmpClause6 = -oij + " " + -kijijP1 + " " + -kijijM1 + " 0\n";
        //writer.append(tmpClause6);


        // Top-Right Corner
        i = 1;
        j = this.size;
        oij =  this.size * this.size + (i -1) * this.size + j;
        kijiP1j = 3 * this.size * this.size +i * this.size + j;
        //kijiM1j = 2 * this.size * this.size + (i - 2) * this.size + j;
        //kijijP1 = 5 * this.size * this.size + (i - 1) * this.size + j+1;
        kijijM1 = 4 * this.size * this.size + (i - 1) * this.size + j-1;
        tmpClause = -oij + " " + kijiP1j + " " + kijijM1 + " 0\n";
        writer.append(tmpClause);
        //tmpClause1 = -oij + " " + -kijiP1j + " " + -kijiM1j + " 0\n";
        //writer.append(tmpClause1);
        //tmpClause2 = -oij + " " + -kijiP1j + " " + -kijijP1 + " 0\n";
        //writer.append(tmpClause2);
        tmpClause3 = -oij + " " + -kijiP1j + " " + -kijijM1 + " 0\n";
        writer.append(tmpClause3);
        //tmpClause4 = -oij + " " + -kijiM1j + " " + -kijijP1 + " 0\n";
        //writer.append(tmpClause4);
        //tmpClause5 = -oij + " " + -kijiM1j + " " + -kijijM1 + " 0\n";
        //writer.append(tmpClause5);
        //tmpClause6 = -oij + " " + -kijijP1 + " " + -kijijM1 + " 0\n";
        //writer.append(tmpClause6);


    }


    private int indexOf(int[] arr, int a){
        int i = -1;
        for(int j=0; j<arr.length; j++){
            if(a==Math.abs(arr[j]))
                i = j;
        }
        return i;
    }

// adaptSolution is the MEMIR PELET (I dont know how to write in english this
// It accepts as input the solution (HASAMA) to the CNF SAT (PASUK) and
// reconstructs the board with its newly created tents
    public String adaptSolution(int[] sol) {
        int oij = 0;
        int tij = 0;
        int tmpPrevVal;
        for (int i = 1; i <= this.size; i++) {
            for (int j = 1; j <= this.size; j++) {
                oij = this.size * this.size + (i - 1) * this.size + j;
                tij = (i - 1) * this.size + j;
                if (sol[oij - 1] > 0){
                    tmpPrevVal = this.board[i-1][j-1];
                    this.board[i-1][j-1] = 2;
                    // This check makes sure board[i-1][j-1] is a new tent and not a tent given as part of the input
                    /*if (tmpPrevVal != 2) {
                            this.horizontal_tents[j - 1]--;
                            this.vertical_tents[i - 1]--;
                    }*/
                }
                if(sol[tij - 1] > 0){
                    // To fix: New trees should not be added. This is a test to make sure all is OK
                    this.board[i-1][j-1] = 1;
                }
            }
        }
        String sij = "";
        int xik = 0;
        /*for(int i = 1; i <= this.size; i++) {
            for (int j = 1; j <= this.size; j++) {
                sij = sij.concat("i =" + i + ",j =" + j + ":\n");
                for(int k = 1; k<=this.size-1; k++) {
                    sij = sij.concat("k =" + k + ":\n");
                    xik = 6 * this.size * this.size + (i - 1) * this.size + k + 1;
                    int x = indexOf(sol, xik);
                    if(sol[x]>0){
                        for(int g=1; g<=k; g++){
                            for(int l=1; l<=ourLogSquare(); l++){
                                int ajgl = 4 * this.size *this.size * this.size + 8 *this.size * this.size + (g-1) * ourLogSquare() + l;
                                int a = indexOf(sol, ajgl);
                                if(sol[a]>0)
                                    sij = sij.concat("1");
                                else
                                    sij = sij.concat("0");
                            }
                            sij = sij.concat(", ");
                        }
                    }
                }
            }

        }*/
        return sij;
    }


    public String adaptSolutionlp(MPVariable[][][] sol) {
        for (int i = 1; i <= this.size; i++) {
            for (int j = 1; j <= this.size; j++) {
                for(int k = 0; k < 4; k++){
                  if(sol[i][j][k].solutionValue() == 1){
                      this.board[i-1][j-1] = 2;
                  }
                }
            }
        }
        String sij = "";
        return sij;
    }

}