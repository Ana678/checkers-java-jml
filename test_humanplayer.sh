#!/bin/bash

# filepath: /home/ana/projeto-logica/test_humanplayer.sh

# Test constructor HumanPlayer
echo "Testing constructor HumanPlayer..."
../OpenJML/openjml --esc --source-path . --method=HumanPlayer HumanPlayer.java Player.java Board.java Piece.java
echo "Finished testing constructor HumanPlayer."

# Test getMove method
echo "Testing getMove method..."
../OpenJML/openjml --esc --source-path . --method=getMove HumanPlayer.java Player.java Board.java Piece.java Move.java
echo "Finished testing getMove method."

# Test makeMove method
echo "Testing makeMove method..."
../OpenJML/openjml --esc --source-path . --method=makeMove HumanPlayer.java
echo "Finished testing makeMove method."

# Test validateMove method
echo "Testing validateMove method..."
../OpenJML/openjml --esc --source-path . --method=validateMove HumanPlayer.java
echo "Finished testing validateMove method."

# Test selectPiece method
echo "Testing selectPiece method..."
../OpenJML/openjml --esc --source-path . --method=selectPiece HumanPlayer.java
echo "Finished testing selectPiece method."
