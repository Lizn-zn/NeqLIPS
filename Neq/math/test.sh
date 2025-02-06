#!/bin/bash

# Define the paths
IN_DIR="Test"
EXPECTED_DIR="Test"

# Mute lake output
lake build > /dev/null 2>&1

# Iterate over each .lean file in the test directory
for infile in $IN_DIR/*.lean; do
    # print the name of infile
    # Extract the base filename without the extension
    base=$(basename "$infile" .lean)

    # Define the path for the expected output file
    expectedfile="$EXPECTED_DIR/$base.expected"

    # Check if the expected output file exists
    if [ ! -f $expectedfile ]; then
        echo "Expected output file $expectedfile does not exist. Skipping $infile."
        continue
    fi

    # Run the command and store its output in a temporary file
    # tmpfile=$(mktemp)
    tmpfile="$EXPECTED_DIR/$base.tmp"
    lake env lean $infile > $tmpfile 2>&1

    # Compare the output with the expected output
    if diff "$tmpfile" "$expectedfile"; then
        echo "$base: PASSED"
        # Remove the temporary file
        rm "$tmpfile"
    else
        echo "$base: FAILED"
        # Remove the temporary file
        rm "$tmpfile"
        exit 1
    fi

done
