#!/bin/bash

# filepath: /home/ana/projeto-logica/test_aiplayer.sh

# Test constructor AIPlayer
echo "Testing constructor AIPlayer..."
../OpenJML/openjml --esc --source-path . --method=AIPlayer AIPlayer.java Player.java Board.java Piece.java
echo "Finished testing constructor AIPlayer."

# Test getMove method
echo "Testing getMove method..."
../OpenJML/openjml --esc --source-path . --method=getMove AIPlayer.java
echo "Finished testing getMove method."

# Test getPossibleMoves method
echo "Testing getPossibleMoves method..."
../OpenJML/openjml --esc --source-path . --method=getPossibleMoves AIPlayer.java
echo "Finished testing getPossibleMoves method."

# Test getBestMovesForPieces method
echo "Testing getBestMovesForPieces method..."
../OpenJML/openjml --esc --source-path . --method=getBestMovesForPieces AIPlayer.java
echo "Finished testing getBestMovesForPieces method."

# Test getMaxJumpMove method
echo "Testing getMaxJumpMove method..."
../OpenJML/openjml --esc --source-path . --method=getMaxJumpMove AIPlayer.java
echo "Finished testing getMaxJumpMove method."

# Test getBestMove method
echo "Testing getBestMove method..."
../OpenJML/openjml --esc --source-path . --method=getBestMove AIPlayer.java
echo "Finished testing getBestMove method."

# Test getKeyByValue method
echo "Testing getKeyByValue method..."
../OpenJML/openjml --esc --source-path . --method=getKeyByValue AIPlayer.java
echo "Finished testing getKeyByValue method."
