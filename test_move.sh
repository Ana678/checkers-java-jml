#!/bin/bash

# filepath: /home/davi/OpenJML/checkers-java-jml/test_move.sh

# Test constructor Move(int x1, int y1, int x2, int y2, Move precedingMove, boolean isJump)
echo "Testing constructor Move(int x1, int y1, int x2, int y2, Move precedingMove, boolean isJump)..."
../OJ/openjml --esc --source-path . --method=Move Move.java
echo "Finished testing constructor Move(int x1, int y1, int x2, int y2, Move precedingMove, boolean isJump)."

# Test getStartingPosition method
echo "Testing getStartingPosition method..."
../OJ/openjml --esc --source-path . --method=getStartingPosition Move.java
echo "Finished testing getStartingPosition method."

# Test getEndingPosition method
echo "Testing getEndingPosition method..."
../OJ/openjml --esc --source-path . --method=getEndingPosition Move.java
echo "Finished testing getEndingPosition method."

# Test getJumpedPieces method
echo "Testing getJumpedPieces method..."
../OJ/openjml --esc --source-path . --method=getJumpedPieces Move.java
echo "Finished testing getJumpedPieces method."

# Test calculateMeanTile method
echo "Testing calculateMeanTile method..."
../OJ/openjml --esc --source-path . --method=calculateMeanTile Move.java
echo "Finished testing calculateMeanTile method."