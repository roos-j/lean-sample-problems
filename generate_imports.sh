#!/bin/bash

LEAN_DIR="LeanSampleProblems"
OUTPUT_FILE="LeanSampleProblems.lean"
MODULE_PREFIX="LeanSampleProblems"

> "$OUTPUT_FILE"

echo "/- This file is auto-generated. Any changes will be overwritten -/" >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"

# Loop over .lean files and write import lines
for filepath in "$LEAN_DIR"/*.lean; do
    filename=$(basename "$filepath" .lean)
    echo "import $MODULE_PREFIX.$filename" >> "$OUTPUT_FILE"
done

echo "" >> "$OUTPUT_FILE"
echo "set_option linter.dupNamespace false" >> "$OUTPUT_FILE"

echo "Import file created: $OUTPUT_FILE"
