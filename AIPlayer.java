import java.util.HashMap;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Random;
/**
 * Responsible for the checkers artifical intelligence.
 * 
 * @author Mckenna Cisler 
 * @version 11.24.2015
 */
public class AIPlayer extends Player
{
    // global variables
    //@ spec_public
    boolean isWhite;

    /**
     * Constructor for objects of class AIPlayer.
     * Initializes this AI's color.
     * @param color This "player's" color.
     */
    //@ ensures this.isWhite == isWhite;
    //@ pure
    public AIPlayer(boolean isWhite)
	{
		this.isWhite = isWhite;
    }

    /**
     * Gets a move, generated by the AI.
     * @param board The board to apply the move to
     * @return Returns the board, modified according to the computer's move
     */
    //@ also requires board != null;
    //@ ensures \result == board;
    public Board getMove(Board board)
    {
        // create list of possible pieces and their moves
        HashMap<Piece, Move[]> possibleChoices = getPossibleMoves(board);
        /*@ nullable @*/ Piece furthestBackwardPiece = null;
        /*@ nullable @*/ Piece furthestForwardPiece = null;

        if (!possibleChoices.isEmpty()) {

            // record furthest back and furthest forward peice to alternate between (just assign the first for now)
            furthestBackwardPiece = possibleChoices.keySet().toArray(new Piece[1])[0]; // convert to array to make it work
            furthestForwardPiece = possibleChoices.keySet().toArray(new Piece[1])[0];
            
        }
        // iterate over our collected possibilites, looking for the best canidate 
        // (based on second answer here: http://stackoverflow.com/questions/1066589/iterate-through-a-hashmap)
        HashMap<Move, Piece> bestMovesPerPiece = getBestMovesForPieces(possibleChoices, furthestBackwardPiece, furthestForwardPiece, board);

        Move bestMove = getBestMove(bestMovesPerPiece, board);

        return applyBestMove(board, bestMove, bestMovesPerPiece);
    }
    
    /**
     * Get all the possible moves for the AI on the board.
     * @param board The board to check for possible moves.
     * @return A map of pieces with their possible moves.
     */
    //@ requires board != null;
    //@ requires board.size >= 0 && board.size < Integer.MAX_VALUE;
    //@ ensures \result != null;
    //@ ensures board == \old(board);  
    //@ assignable \nothing;
    //@ pure
    public HashMap<Piece, Move[]> getPossibleMoves(Board board)
    {
        HashMap<Piece, Move[]> possibleChoices = new HashMap<>();

        //@ loop_invariant 0 <= x && x <= board.size;
        //@ decreases board.size - x;
        for (int x = 0; x < board.size; x++)
        {
            //@ loop_invariant 0 <= y && y <= board.size;
            //@ decreases board.size - y;
            for (int y = 0; y < board.size; y++)
            {
                /*@ nullable @*/ Piece piece = board.getValueAt(x, y);
                if (piece != null && piece.isWhite == this.isWhite)
                {
                    Move[] possibleMoves = piece.getAllPossibleMoves(board);
                    if (possibleMoves != null)                        
                        possibleChoices.put(piece, possibleMoves);
                }
            }
        }
        
        return possibleChoices;
    }

    /**
     * Get the best moves for each piece, considering jumps and positions.
     * @param possibleChoices A map of pieces and their possible moves.
     * @param furthestBackwardPiece The piece furthest back in position.
     * @param furthestForwardPiece The piece furthest forward in position.
     * @return A map of the best moves for each piece.
     */
    //@ requires possibleChoices != null;
    //@ requires board != null;
    //@ ensures \result != null;
    private HashMap<Move, Piece> getBestMovesForPieces(HashMap<Piece, Move[]> possibleChoices, 
                                                        Piece furthestBackwardPiece, 
                                                        Piece furthestForwardPiece,
                                                        Board board)
    {
        HashMap<Move, Piece> bestMovesPerPiece = new HashMap<>();
        
        for (Piece piece : possibleChoices.keySet())
        {
            int thisPieceY = piece.getCoordinates()[1];
            if (thisPieceY > furthestForwardPiece.getCoordinates()[1])
            {
                if (isWhite)
                    furthestForwardPiece = piece;
                else
                    furthestBackwardPiece = piece;
            }
            else if (thisPieceY < furthestBackwardPiece.getCoordinates()[1])
            {
                if (isWhite)
                    furthestBackwardPiece = piece;
                else
                    furthestForwardPiece = piece;
            }
            
            Move[] possibleMoves = possibleChoices.get(piece);
            Move maxJumpMove = getMaxJumpMove(possibleMoves, board);
            
            bestMovesPerPiece.put(maxJumpMove, piece);
        }
        
        return bestMovesPerPiece;
    }

    /**
     * Get the move with the maximum number of jumps.
     * @param possibleMoves An array of possible moves for a piece.
     * @return The move with the most jumps.
     */
    //@ requires possibleMoves != null && possibleMoves.length > 0;
    //@ requires board != null;
    //@ ensures \result != null;
    private Move getMaxJumpMove(Move[] possibleMoves, Board board)
    {
        Move maxJumpMove = possibleMoves[0];
        int maxJumpMoveLength = 0;
        
        //@ loop_invariant 0 <= i && i <= possibleMoves.length;
        //@ loop_invariant (\forall int j; 0 <= j && j < i; 
        //@    possibleMoves[j].x1 >= 0 && possibleMoves[j].x2 >= 0 && possibleMoves[j].y1 >= 0 && possibleMoves[j].y2 >= 0);
        //@ decreases possibleMoves.length - i;
        for (int i = 0; i < possibleMoves.length; i++)
        {    
            //@ assert possibleMoves[i].x1 >= 0 && possibleMoves[i].x2 >= 0 && possibleMoves[i].y1 >= 0 && possibleMoves[i].y2 >= 0; 

            /*@ nullable @*/ Piece[] jumpedPieces = possibleMoves[i].getJumpedPieces(board);
            if (jumpedPieces != null)
            {
                int jumpLength = jumpedPieces.length;
                if (jumpLength >= maxJumpMoveLength)
                {
                    maxJumpMoveLength = jumpLength;
                    maxJumpMove = possibleMoves[i];
                }
            }
        }
        
        return maxJumpMove;
    }

    /**
     * Get the best move from the best moves found for each piece.
     * @param bestMovesPerPiece A map of the best moves for each piece.
     * @return The best overall move.
     */
    //@ requires bestMovesPerPiece != null;
    //@ ensures \result != null;
    private Move getBestMove(HashMap<Move, Piece> bestMovesPerPiece, Board board)
    {
        Move absoluteBestMove = bestMovesPerPiece.keySet().toArray(new Move[1])[0];
        int absoluteBestMoveJumpLength = 0;
        
        for (Move move : bestMovesPerPiece.keySet())
        {
            Piece[] jumpedPieces = move.getJumpedPieces(board);
            if (jumpedPieces != null)
            {
                int thisBestMoveJumpLength = jumpedPieces.length;
                if (thisBestMoveJumpLength >= absoluteBestMoveJumpLength)
                {
                    absoluteBestMoveJumpLength = thisBestMoveJumpLength;
                    absoluteBestMove = move;
                }
            }
        }
        
        return absoluteBestMove;
    }


    /**
     * Apply the best move to the board.
     * @param board The board to apply the move to.
     * @param bestMove The best move to apply.
     * @param bestMovesPerPiece A map of best moves for each piece.
     * @return The board, modified according to the computer's move.
     */
    //@ requires board != null && bestMove != null && bestMovesPerPiece != null;
    //@ ensures \result == board;
    private Board applyBestMove(Board board, Move bestMove, HashMap<Move, Piece> bestMovesPerPiece)
    {
        int absoluteBestMoveJumpLength = bestMove.getJumpedPieces(board).length;
        
        if (absoluteBestMoveJumpLength > 0)
        {
            board.applyMoveToBoard(bestMove, bestMovesPerPiece.get(bestMove));
        }
        else
        {
            int randomNum = new Random().nextInt(2);
            Piece furthestBackwardPiece = bestMovesPerPiece.get(bestMove);
            Piece furthestForwardPiece = bestMovesPerPiece.get(bestMove);
            if (randomNum == 0)
            {
                board.applyMoveToBoard(getKeyByValue(bestMovesPerPiece, furthestBackwardPiece), furthestBackwardPiece);
            }
            else
            {
                board.applyMoveToBoard(getKeyByValue(bestMovesPerPiece, furthestForwardPiece), furthestForwardPiece);
            }  
        }
        
        return board;
    }


    /**
     * Note: copied from http://stackoverflow.com/a/2904266
     * Returns a key in a hashmap that correpsonds to the given value
     * @param map The map to search in
     * @param value The value to search for
     * @return Returns the key found in the map, may be null if not found
     */
    //@ requires map != null;
    //@ pure
    private  /*@ nullable @*/  <T, E> T getKeyByValue(HashMap<T, E> map, E value) 
    {
        for (Entry<T, E> entry : map.entrySet()) 
        {

            if (Objects.equals(value, entry.getValue())) 
            {
                return entry.getKey();
            }
        }
        return null;
    }
}
