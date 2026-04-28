#!/bin/bash

# Check if directory argument is provided
if [ -z "$1" ]; then
    echo "Usage: $0 <directory>"
    echo "Example: $0 IntArrayClaude"
    exit 1
fi

DIR=$1

# Check if directory exists
if [ ! -d "$DIR" ]; then
    echo "Error: Directory '$DIR' does not exist."
    exit 1
fi

# Count the number of coins*.v files
COUNT=$(find "$DIR" -maxdepth 1 -name "coins*.v" | wc -l)

echo "Found $COUNT coins*.v file(s) in $DIR"