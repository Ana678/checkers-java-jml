import java.util.ArrayList;
import java.util.Arrays;
/**
 * A class representing a game piece, and handling interactions with it.
 * 
 * @author Mckenna Cisler
 * @version 11.23.2015
 */
public class Piece
{
    public int x; 
    public int y; 
    public boolean isKing = false;
    public boolean isWhite;

    //@ public invariant x>=0 && y>=0;
    //@ public invariant x + y < Integer.MAX_VALUE;

    /**
     * Constructor for objects of class Piece
     * Initializes position and color.
     * @param x The x position of this piece.
     * @param y The y position of this piece.
     * @param isWhite Whether this piece is white or black.
     */
    //@ public normal_behavior
    //@     requires x >=0 && y>=0;
    //@     requires x + y < Integer.MAX_VALUE;
    //@     ensures this.x == x;
    //@     ensures this.y == y;
    //@     ensures this.isWhite == isWhite;
    //@ pure
    public Piece(int x, int y, boolean isWhite)
    {
        this.x = x;
        this.y = y;
        this.isWhite = isWhite;
    }

    /**
     * @return Returns a two-part array representing the coordinates of this piece's position.
     */
    //@ ensures \result != null;
    //@ ensures \result.length==2;
    //@ ensures \result[0] == this.x;
    //@ ensures \result[1] == this.y;
    //@ ensures \result[0] >=0;
    //@ ensures \result[1] >=0;
    //@ pure
    public int[] getCoordinates()
    {
        int[] coordinates = new int[2];
        coordinates[0] = this.x;
        coordinates[1] = this.y;
        return coordinates;
    }
    
    /**
     * @return Returns a string representation of this given piece
     */
    //@ ensures \result.length()==2;
    //@ ensures (this.isWhite && this.isKing) ==> (\result.equals("WK"));
    //@ ensures (this.isWhite && !this.isKing) ==> (\result.equals("W "));
    //@ ensures (!this.isWhite && this.isKing) ==> (\result.equals("BK"));
    //@ ensures (!this.isWhite && !this.isKing) ==> (\result.equals("B "));
    //@ pure
    public String getString()
    {
        String baseSymbol;

        if (isWhite)
            baseSymbol = "W";
        else
            baseSymbol = "B";

        //@ assert baseSymbol.length()==1;
        if (isKing)
            baseSymbol += "K";
        else
            baseSymbol += " "; // add a space in the non-king state just to keep consistency

        return baseSymbol;
    }

    /**
     * Switches this piece to a king (TODO: MAY BE UNNECCESARY DUE TO BELOW METHOD!!)
     */
    //@ assignable this.isKing;
    //@ ensures this.isKing;
    private void setKing()
    {
        this.isKing = true;
    }
    
    /**
     * Switches this peice to be a king if it is at the end of the board.
     * Should be called after every move.
     */
    //@ assignable this.isKing;
    //@ ensures board != null;
    public void checkIfShouldBeKing(Board board)
    {
        // if the piece is white, it's a king if it's at the +y, otherwise if its black this happens at the -y side
        if (isWhite && this.y == board.size - 1 || 
            !isWhite && this.y == 0)
            this.setKing();
    }

    /**
     * Moves this piece's reference of its position (DOES NOT ACTUALLY MOVE ON BOARD)
     * @param x The x coordinate of the move
     * @param y The y coordinate of the move
     */
    //@ assignable this.x, this.y;
    //@ requires x >= 0 && y >= 0;
    //@ requires x + y < Integer.MAX_VALUE;
    //@ ensures this.x==x;
    //@ ensures this.y==y;
    public void moveTo(int x, int y)
    {
        this.x = x;
        this.y = y;
    }
    
    /**
     * Generates all physically possible moves of the given piece.
     * (Only actually generates the non-jumping moves - jumps are done recusively in getAllPossibleJumps)
     * @return Returns a list of all the moves (including recusively found jumps), including each individual one involved in every jump.
     * @param board The board to work with - assumed to be flipped to correspond to this piece's color.
     */

    //@ requires board != null;
    //@ requires this.x >= 0 && this.y >= 0;
    //@ requires this.x <= 9 && this.y <= 9;
    //@ ensures (\result == null) || (\forall int i; 0 <= i && i < \result.length; \result[i] != null);
    //@ pure
    public /*@ nullable @*/Move[] getAllPossibleMoves(Board board)
    {
        // create expandable list of all moves
        ArrayList<Move> moves = new ArrayList<Move>();
        
        // change y endpoints based on kingness and color=direction of movement
        int startingY, yIncrement;
        if (isWhite)
        {
            // if it's white, we move from further down the board backwards to possible king position
            startingY = this.y + 1; 
            yIncrement = -2;
        }
        else 
        {
            // if it's black, we move from further up the board forward to possible king position
            startingY = this.y - 1;
            yIncrement = 2;
        }
        
        // use kingess to determine number of rows to check
        int rowsToCheck = 1; // default as non-king
        if (this.isKing)
            rowsToCheck = 2;
        
        // iterate over the four spaces where normal (non-jumping) moves are possible  
        //@ maintaining (this.x+1+2 >= x_it >= (this.x-1));
        //@ decreases this.x + 1 - x_it;      
        for (int x_it = this.x - 1; x_it <= this.x + 1; x_it += 2)
        {
            // go over the rows (or row) (we iterate the number of times determined by the kingess above)
            int y = startingY - yIncrement; // add this so we can add the normal increment before the boundary checks
            //@ maintaining 0 <= i && i <= rowsToCheck;
            //@ decreases rowsToCheck - i;
            for (int i = 0; i < rowsToCheck; i++) 
            {
                if (y > Integer.MAX_VALUE - 2 || y < Integer.MIN_VALUE + 2) {
                    return null;
                }
                // increment y if we need to (this will have no effect if we only run one iteration)
                y += yIncrement;
                
                // check for going off end of board, in which case just skip this iteration (we may do this twice if at a corner)
                if (board.isOverEdge(x_it, y))
                    continue;
                
                // add a move here if there's not a piece 
                if (board.getValueAt(x_it, y) == null)
                {
                    if(this.x+x_it>Integer.MAX_VALUE || this.y+y>Integer.MAX_VALUE || this.x+x_it<Integer.MIN_VALUE || this.y+y<Integer.MIN_VALUE){
                        return null;
                    }
                    // this is not jump move in any case, and is always the first move
                    moves.add(new Move(this.x, this.y, x_it, y, null, false)); 
                }
            }
        }
        
        // after we've checked all normal moves, look for and add all possible jumps (recusively as well - I mean ALL jumps)
        /*@ nullable @*/Move[]possibleJumps = this.getAllPossibleJumps(board, null);
        if (possibleJumps != null)
            moves.addAll(Arrays.asList(possibleJumps));

        // IF there are some moves, shorten and return ArrayList as a normal array
        if (!moves.isEmpty())
        {
            moves.trimToSize();
            return moves.toArray(new Move[1]); // convert to Move objects
        }
        else 
            return null; // return null otherwise to symbolize no moves
    }
    
    /**
     * Finds all jumping moves originating from this piece.
     * Does this recursivly; for each move a new imaginary piece will be generated,
     * and this function will then be called on that piece to find all possible subsequent moves.
     * @param board The board to work with - assumed to be flipped to correspond to this piece's color.
     * @param precedingMove The moves preceding the call to search for moves off this piece - only used
     * in recursion, should be set to null at first call. (if it's not, it means this piece is imaginary).
     */

    //@ requires board != null;
    //@ requires this.x >= 0 && this.y >= 0;
    //@ requires this.x <= 9 && this.y <= 9;
    //@ ensures (\result == null) || (\forall int i; 0 <= i && i < \result.length; \result[i] != null);
    //@ pure
    private /*@ nullable @*/ Move[] getAllPossibleJumps(Board board, /*@ nullable @*/Move precedingMove)
    {
        // create expandable list of all moves
        ArrayList<Move> moves = new ArrayList<Move>();
        
        // this is the same as above except we're doing a large cube (4x4)
        // change y endpoints based on kingness and color=direction of movement
        int startingY, yIncrement;
        if (isWhite)
        {
            // if it's white, we move from further down the board backwards to possible king position
            startingY = this.y + 2;
            yIncrement = -4;
        }
        else 
        {
            // if it's black, we move from further up the board forward to possible king position
            startingY = this.y - 2;
            yIncrement = 4;
        }
        
        // use kingness to determine number of rows to check
        int rowsToCheck = 1; // default as non-king
        if (this.isKing)
            rowsToCheck = 2;
        
        // iterate over the four spaces where normal (non-jumping) moves are possible        
        //@ maintaining ((this.x+2+4) >= x_it >= (this.x-2));
        //@ decreases this.x + 2 - x_it;
        for (int x_it = this.x - 2; x_it <= this.x + 2; x_it += 4)
        {
            // go over the rows (or row) (we iterate the number of times determined by the kingess above)
            int y = startingY - yIncrement; // add this so we can add the normal increment before the boundary checks in the loop
            
            //@ maintaining 0 <= i && i <= rowsToCheck;
            //@ decreases rowsToCheck - i;
            for (int i = 0; i < rowsToCheck; i++) 
            {
                // increment y if we need to (this will have no effect if we only run one iteration)
                // assume y + yIncrement <= Integer.MAX_VALUE && y + yIncrement >= Integer.MIN_VALUE;
                if (y > Integer.MAX_VALUE - 4 || y < Integer.MIN_VALUE + 4) {
                    return null;
                }
                y += yIncrement;
                
                // check for going off end of board, in which case just skip this iteration (we may do this twice if at a corner)
                if (board.isOverEdge(x_it, y))
                    continue;
                
                // don't try to go backward to our old move start so we don't get in infinite recursion loops
                if (precedingMove != null &&
                    x_it == precedingMove.getStartingPosition()[0] && 
                    y == precedingMove.getStartingPosition()[1])
                    continue;
                
                // test if there is a different-colored piece between us (at the average of our position) and the starting point 
                // AND that there's no piece in the planned landing space (meaning we can possible jump there)
                int xBetween = (this.x + x_it)/2;
                int yBetween = (this.y + y)/2;
                if(xBetween >= board.size || yBetween >= board.size || xBetween < 0 || yBetween < 0){
                    return null;
                }
                
                /*@ nullable @*/Piece betweenPiece = board.getValueAt(xBetween, yBetween );
                if (betweenPiece != null &&
                    betweenPiece.isWhite != this.isWhite &&
                    board.getValueAt(x_it, y) == null)
                {
                    // in which case, add a move here, and note that it is a jump (we may be following some other jumps)
                    Move jumpingMove = new Move(this.x, this.y, x_it, y, precedingMove, true); // origin points are absolute origin (ORIGINAL piece)
                    
                    // then add it to our list
                    moves.add(jumpingMove);
                      
                    // after jumping, create an imaginary piece as if it was there to look for more jumps
                    Piece imaginaryPiece = new Piece(x_it, y, this.isWhite);
                    
					// correspond possible jumps to this piece's kingness
               		if (this.isKing) imaginaryPiece.setKing();
                    
                    // find possible subsequent moves recusivly
                    /*@ nullable @*/Move[] subsequentMoves = imaginaryPiece.getAllPossibleJumps(board, jumpingMove);
                    
                    // add these moves to our list if they exist, otherwise just move on to other possibilities
                    if (subsequentMoves != null)
                        moves.addAll(Arrays.asList(subsequentMoves));
                }
            }
        }

        // IF there are some moves, shorten and return ArrayList as a normal array
        if (!moves.isEmpty())
        {
            moves.trimToSize();
            return moves.toArray(new Move[1]); // convert to Move arrays
        }
        else 
            return null; // return null otherwise to symbolize no moves
    }
}