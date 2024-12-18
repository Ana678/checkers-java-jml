import java.util.Scanner;
/**
 * Responsible for determining the gamemode (1- or 2-player), running the game, and handling game exit.
 * 
 * @author Mckenna Cisler 
 * @version 11.23.2015
 */
public class GameRunner
{
    // game constants
    public static final int SIZE = 9;

    // define globally used variables
    private static Scanner input = new Scanner(System.in);
    private static boolean isPlayer1 = true;
    
    // define an easily accesible "end" variable
    private static boolean endGameNow = false;
    

    public static void main(String[] args)
    {
        // generate basic board and setup
        Board board = new Board(SIZE);

        // define abstract classes, to be assigned a concrete class after deciding gamemode
        Player player1;
        Player player2;

        if (askIfTwoPlayer())
        {
            player1 = new HumanPlayer(true);
            player2 = new HumanPlayer(false);
        }
        else 
        {         
            player1 = new HumanPlayer(true);
            player2 = new AIPlayer(false);
        }
        clearScreen();

        while ( !endGame(board) )
        {          
            if (isPlayer1)
            {
                board = player1.getMove(board);
            }
            else
            {
                board = player2.getMove(board);
            }

            // switch players and flip board for next player
            isPlayer1 = !isPlayer1;
            //board = board.getFlippedBoard();
        }
    }

    /**
     * Queries the user to determine the requested gamemode
     * @return Returns true if the user wants two-player mode, 
     * else false if they want one-player mode.
     */
    //@ requires input != null;
    //@ ensures \result == true || \result == false;
    private static boolean askIfTwoPlayer()
    {       
        // keep asking to get a valid response
        //@ loop_invariant true; 
        while (true)
        {
            displayWelcomeMessage();

            // ask for String, but only accept "1" or "2"
            String response = input.nextLine().trim();

            if (response.equals("1")) {
                return false;
            } else if (response.equals("2")) {
                return true;
            } else if (response.equals("exit")) {
                endGameNow();
                return true;
            }
            // Mensagem de erro se entrada inválida
            System.out.println("Invalid input. Please enter '1', '2', or 'exit'.");
            continue;
        }
    }

    /**
     * Determines whether the game has been completed, or is in a stalemate
     * @param board The board to check to determine if we're at an endgame point.
     */
    //@ requires board.size < Integer.MAX_VALUE && board.size*board.size < Integer.MAX_VALUE;
    //@ assignable System.out.outputText, System.out.eol;
    //@ code_java_math
    private static boolean endGame(Board board)
    {
        // have an emergency trigger for endgame
        if (endGameNow)
            return true;
        else
        {
            // otherwise search the board for pieces of both colors, and if none of one color are present,
            // the other player has won.
            int movableWhiteNum = 0;
            int movableBlackNum = 0;
            
            //@ loop_invariant 0 <= pos && pos <= board.size*board.size;
            //@ decreases board.size*board.size - pos;
            for (int pos = 0; pos < board.size*board.size; pos++)
            {
                // make sure the piece exists, and if so sum movable pieces for each color)
                /*@ nullable @*/ Piece pieceHere = board.getValueAt(pos);
                if (pieceHere != null)
                {
                    //@ assume pieceHere.x <= 9 && pieceHere.y <= 9;
                    // only consider piece if it has possible moves
                    /*@ nullable @*/ Move[] movesHere = pieceHere.getAllPossibleMoves(board);
                    if (movesHere != null && movesHere.length > 0)
                    {
                        if (pieceHere.isWhite)
                            movableWhiteNum++;
                        else if (!pieceHere.isWhite)
                            movableBlackNum++;
                    }
                }
            }
            
            // determine if anyone won (or if no one had any moves left)
            if (movableWhiteNum + movableBlackNum == 0)
                System.out.println("The game was a stalemate...");
            else if (movableWhiteNum == 0)
                System.out.println("Congratulations, Black, you have won the game gloriously!");
            else if (movableBlackNum == 0)
                System.out.println("Congratulations, White, you have won the game gloriously!");
            else
                return false;
            
            // we can only make it here if any of the above conditions are hit
            return true;
        }
    }
    
    //@ ensures true;
    //@ assignable System.out.outputText, System.out.eol;
    private static void displayWelcomeMessage() {
        clearScreen();
        System.out.println("*******Welcome to checkers!*******\n");
        System.out.println("Enter 'exit' to exit at any point (or 0 when moving a piece).\n");
        System.out.println("We offer two game modes:");
        System.out.println("[1] 1 Player Mode (vs Computer) - EXPERIMENTAL");
        System.out.println("[2] 2 Player Mode");
        System.out.println("\nWhich one would you like to play? Enter a number: ");
    }

    /**
     * Responsible for quickly ending the game
     */
    public static void endGameNow()
    {
        endGameNow = true;
    }
    
    /**
     * Clears the terminal screen
     */
    //@ assignable System.out.outputText, System.out.eol;
    public static void clearScreen()
    {
    	// see http://stackoverflow.com/a/32008479/3155372
        System.out.print("\033[2J\033[1;1H");
    }
}
