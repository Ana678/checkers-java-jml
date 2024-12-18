#!/bin/bash

# filepath: /home/ana/projeto-logica/test_player.sh

# Test constructor Player
echo "Testing constructor Player..."
../OpenJML/openjml --esc --source-path . --method=Player Player.java Board.java Piece.java
echo "Finished testing constructor Player."

# Test getMove method in AI class
echo "Testing getMove method in AI class..."
../OpenJML/openjml --esc --source-path . --method=getMove AIPlayer.java Player.java Board.java Piece.java
echo "Finished testing getMove method in AI class."
