import java.util.ArrayList;
import java.util.Arrays;
/**
 * Represents a single move of a piece.
 * 
 * @author Mckenna Cisler
 * @version 12.1.2015
 */
//@ nullable_by_default
public class Move
{
    //@ spec_public
    int x1, y1, x2, y2;
    //@ spec_public
    Move precedingMove;
    //@ spec_public
    boolean isJump;
    
    //@ public invariant x1 >= 0 && x2 >= 0 && y1 >= 0 && y2 >= 0;
    //@ public invariant (x1 + x2) < Integer.MAX_VALUE && (y1 + y2) < Integer.MAX_VALUE;
    /**
     * Constructor for objects of class Move - initializes starting and final position.
     * @param x1 Starting x position.
     * @param y1 Starting y position.
     * @param x2 Ending x position.
     * @param y2 Ending y position.
     * @param precedingMove The move preceding this one (can be null if move is first)
     */

    //@ public normal_behavior
    //@     requires x1 >=0 && x2>=0 && y1 >=0 && y2>=0;
    //@     requires (x1+x2) < Integer.MAX_VALUE && (y1+y2) < Integer.MAX_VALUE;
    //@     ensures this.x1 == x1;
    //@     ensures this.x2 == x2;
    //@     ensures this.y1 == y1;
    //@     ensures this.y2 == y2;
    //@ pure
    public Move(int x1, int y1, int x2, int y2, Move precedingMove, boolean isJump)
    {
        this.x1 = x1;
        this.y1 = y1;
        this.x2 = x2;
        this.y2 = y2;
        this.precedingMove = precedingMove;
        this.isJump = isJump;
    }

    /**
     * @return Returns a two-part array representing the coordinates of this move's starting position.
     */
    //@ ensures \result != null;
    //@ ensures \result.length==2;
    //@ ensures \result[0] == x1;
    //@ ensures \result[1] == y1;
    //@ pure
    public int[] getStartingPosition()
    {
        int[] position = new int[2];
        position[0] = x1;
        position[1] = y1;
        return position;
    }
    
    /**
     * @return Returns a two-part array representing the coordinates of this move's ending position.
     */
    //@ ensures \result != null;
    //@ ensures \result.length==2;
    //@ ensures \result[0] == this.x2;
    //@ ensures \result[1] == this.y2;
    //@ pure
    public int[] getEndingPosition()
    {
        int[] position = new int[2];
        position[0] = x2;
        position[1] = y2;
        return position;
    }

    //@ requires v1 >= 0 && v2 >= 0;
    //@ requires (v1+v2) < Integer.MAX_VALUE;
    //@ ensures \result >= 0;
    //@ pure
    public int calculateMeanTile(int v1,int v2){
        return (int)(v1+v2)/2;
    }

    /**
     * Finds the pieces jumped in this move.
     * (Get's inbetween jumps using recursion)
     * @return Returns an array of pieces that were jumped.
     * @param board The board to look for the pieces on.
     */

    //@ requires board != null;
    //@ requires 0 <= x1 && 0 <= x2 && 0 <= y1 && 0 <= y2;    
    //@ requires (x1 + x2) < Integer.MAX_VALUE;
    //@ requires (y1 + y2) < Integer.MAX_VALUE;
    //@ ensures \result == null || (\forall int i; 0 <= i && i < \result.length; \result[i] != null);
    //@ pure
    public Piece[] getJumpedPieces(Board board)
    {
        if(!this.isJump){
            return null;
        }
        // if this move wasn't a jump, it didn't jump a piece!
        
        // create expandable list of all pieces
        ArrayList<Piece> pieces = new ArrayList<Piece>();
        
        // the piece this move is jumping should be between the start and end of this move
        // (the average of those two positions)
        // assume x1 >= 0 && x2 >= 0 && y1 >= 0 && y2 >= 0;
        int pieceX = calculateMeanTile(x1,x2);
        int pieceY = calculateMeanTile(y1,y2);
        
        // add this most recent jump...
        // assume pieceX<board.size && pieceY<board.size;
        if(pieceX >= board.size || pieceY >= board.size){
            return null;
        }

        Piece jumpedPiece = board.getValueAt(pieceX, pieceY);
        if (jumpedPiece != null)
            if(jumpedPiece.x>=0 && jumpedPiece.y>=0){
                pieces.add(jumpedPiece);
            }
        // ...but also go back to get the inbetween ones (if we're not the first move)
        if (precedingMove != null)
        {
            Piece[] precedingJumpedPieces = precedingMove.getJumpedPieces(board);
            if (precedingJumpedPieces != null)
            {
                for (Piece p : precedingJumpedPieces) {
                    if (p != null) {
                        if(p.x>=0 && p.y>=0 && (long) p.x + (long) p.y < Integer.MAX_VALUE){
                            pieces.add(p);
                        }
                    }
                }
            } 
        }
        
        // shorten and return
        pieces.trimToSize();
        return pieces.toArray(new Piece[1]); // convert to Piece array 
    }

}