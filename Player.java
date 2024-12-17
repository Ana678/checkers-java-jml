
/**
 * An abstract version of a player, from which Human and AI Players will be extended.
 * Used so that both player types can be used interchangably.
 * 
 * @author Mckenna Cisler
 * @version 11.23.2015
 */
public abstract class Player
{
    /**
     * Gets a move, by asking the given player what move they want to do.
     * @param board The board to apply the move to
     * @return Returns the board, modified according to the player's move
     */
    //@ public model instance boolean color;

    // assignable System.out.outputText, System.out.eol, System.in;
    // assignable \everything;
    //@ requires board != null;
    //@ ensures \result == board;
    public abstract Board getMove(Board board);
}
