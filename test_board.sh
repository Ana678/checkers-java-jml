#!/bin/bash

# filepath: /home/davi/OpenJML/checkers-java-jml/test_board.sh

# Test constructor Board
echo "Testing constructor Board..."
../OJ/openjml --esc --source-path . --method=Board Board.java
echo "Finished testing constructor Board."

# Test setupBoard method
echo "Testing setupBoard method..."
../OJ/openjml --esc --source-path . --method=setupBoard Board.java
echo "Finished testing setupBoard method."

# Test applyMoveToBoard method
echo "Testing applyMoveToBoard method..."
../OJ/openjml --esc --source-path . --method=applyMoveToBoard Board.java
echo "Finished testing applyMoveToBoard method."

# Test setValueAt(int x, int y) method
echo "Testing setValueAt1 method..."
../OJ/openjml --esc --source-path . --method=setValueAt1 Board.java
echo "Finished testing setValueAt1 method."

# Test getValueAt method
echo "Testing getValueAt method..."
../OJ/openjml --esc --source-path . --method=getValueAt Board.java
echo "Finished testing getValueAt method."

# Test getCoordinatesFromPosition method
echo "Testing getCoordinatesFromPosition method..."
../OJ/openjml --esc --source-path . --method=getCoordinatesFromPosition Board.java
echo "Finished testing getCoordinatesFromPosition method."

# Test getPositionFromCoordinates method
echo "Testing getPositionFromCoordinates method..."
../OJ/openjml --esc --source-path . --method=getPositionFromCoordinates Board.java
echo "Finished testing getPositionFromCoordinates method."

# Test isCheckerboardSpace method
echo "Testing isCheckerboardSpace method..."
../OJ/openjml --esc --source-path . --method=isCheckerboardSpace Board.java
echo "Finished testing isCheckerboardSpace method."

# Test isOverEdge method
echo "Testing isOverEdge method..."
../OJ/openjml --esc --source-path . --method=isOverEdge Board.java
echo "Finished testing isOverEdgemethod."
