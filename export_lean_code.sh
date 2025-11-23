#!/bin/bash
# Export all Lean code from TDCSG directory into a single text file

OUTPUT_FILE="TDCSG_all_lean_code.txt"

# Clear output file if it exists
> "$OUTPUT_FILE"

# Find all .lean files in TDCSG directory and process them
find TDCSG -name "*.lean" -type f | sort | while read -r file; do
    echo "=================================================================================" >> "$OUTPUT_FILE"
    echo "FILE: $file" >> "$OUTPUT_FILE"
    echo "=================================================================================" >> "$OUTPUT_FILE"
    echo "" >> "$OUTPUT_FILE"
    cat "$file" >> "$OUTPUT_FILE"
    echo "" >> "$OUTPUT_FILE"
    echo "" >> "$OUTPUT_FILE"
done

# Count files processed
num_files=$(find TDCSG -name "*.lean" -type f | wc -l)
echo "Exported $num_files Lean files to $OUTPUT_FILE"
