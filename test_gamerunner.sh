#!/bin/bash

# filepath: /home/ana/projeto-logica/GameRunner.java

# Test main method
echo "Testing main method..."
../OpenJML/openjml --esc --source-path . --method=main GameRunner.java AIPlayer.java Player.java Board.java Piece.java Move.java
echo "Finished testing main method."

# Test askIfTwoPlayer method
echo "Testing askIfTwoPlayer method..."
../OpenJML/openjml --esc --source-path . --method=askIfTwoPlayer GameRunner.java
echo "Finished testing askIfTwoPlayer method."

# Test endGame method
echo "Testing endGame method..."
../OpenJML/openjml --esc --source-path . --method=endGame GameRunner.java
echo "Finished testing endGame method."

# Test displayWelcomeMessage method
echo "Testing displayWelcomeMessage method..."
../OpenJML/openjml --esc --source-path . --method=displayWelcomeMessage GameRunner.java
echo "Finished testing displayWelcomeMessage method."

# Test endGameNow method
echo "Testing endGameNow method..."
../OpenJML/openjml --esc --source-path . --method=endGameNow GameRunner.java
echo "Finished testing endGameNow method."

# Test clearScreen method
echo "Testing clearScreen method..."
../OpenJML/openjml --esc --source-path . --method=clearScreen GameRunner.java
echo "Finished testing clearScreen method."
