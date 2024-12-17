#!/bin/bash

# filepath: /home/davi/OpenJML/checkers-java-jml/test_piece.sh

# Test constructor Piece(int x, int y, boolean isWhite)
echo "Testing constructor Piece(int x, int y, boolean isWhite)..."
../OJ/openjml --esc --source-path . --method=Piece Piece.java
echo "Finished testing constructor Piece(int x, int y, boolean isWhite)."

# Test moveTo method
echo "Testing moveTo method..."
../OJ/openjml --esc --source-path . --method=moveTo Piece.java
echo "Finished testing moveTo method."

# Test getAllPossibleMoves method
echo "Testing getAllPossibleMoves method..."
../OJ/openjml --esc --source-path . --method=getAllPossibleMoves Piece.java
echo "Finished testing getAllPossibleMoves method."

# Test getAllPossibleJumps method
echo "Testing getAllPossibleJumps method..."
../OJ/openjml --esc --source-path . --method=getAllPossibleJumps Piece.java
echo "Finished testing getAllPossibleJumps method."

# Test getString method
echo "Testing getString method..."
../OJ/openjml --esc --source-path . --method=getString Piece.java
echo "Finished testing getString method."

# Test getCoordinates method
echo "Testing getCoordinates method..."
../OJ/openjml --esc --source-path . --method=getCoordinates Piece.java
echo "Finished testing getCoordinates method."

# Test checkIfShouldBeKing method
echo "Testing checkIfShouldBeKing method..."
../OJ/openjml --esc --source-path . --method=checkIfShouldBeKing Piece.java
echo "Finished testing checkIfShouldBeKing method."

# Test setKing method
echo "Testing setKing method..."
../OJ/openjml --esc --source-path . --method=setKing Piece.java
echo "Finished testing setKing method."