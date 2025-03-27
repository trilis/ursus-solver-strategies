#!/bin/bash

# Check if input file is provided
if [ $# -ne 1 ]; then
    echo "Usage: $0 <input_file>"
    exit 1
fi

INPUT_FILE=$1

# Create a temporary file for processed data
TEMP_DATA="timing_data.dat"

# Extract and process the timing data
grep -o "\[.*\] ran for .* secs" "$INPUT_FILE" | while read -r line; do
    # Extract dataset, strategy, size, and time
    dataset=$(echo "$line" | grep -o "\[[^]]*\]" | head -n1 | tr -d '[]')
    strategy=$(echo "$line" | grep -o "\[[^]]*\]" | head -n2 | tail -n1 | tr -d '[]')
    size=$(echo "$line" | grep -o "\[[^]]*\]" | tail -n1 | tr -d '[]')
    time=$(echo "$line" | grep -o "ran for [0-9.]*" | cut -d' ' -f3)
    
    echo "$dataset $strategy $size $time" >> $TEMP_DATA
done

# Create gnuplot script
cat > plot.gnu << 'EOF'
set terminal pngcairo enhanced size 800,600
set grid

# Get unique datasets and strategies
datasets = system("awk '{print $1}' timing_data.dat | sort -u")
strategies = system("awk '{print $2}' timing_data.dat | sort -u")
n_datasets = words(datasets)
n_strategies = words(strategies)

# Set line styles
set style line 1 lc rgb '#0060ad' lt 1 lw 2 pt 7 ps 1.5
set style line 2 lc rgb '#dd181f' lt 1 lw 2 pt 7 ps 1.5
set style line 3 lc rgb '#00ad60' lt 1 lw 2 pt 7 ps 1.5

# Create a plot for each dataset
do for [i=1:n_datasets] {
    dataset = word(datasets, i)
    # Check if there's data for this dataset
    set output sprintf('%s.png', dataset)
    set title sprintf('Performance Comparison for Dataset: %s', dataset)
    set xlabel 'Dataset Size'
    set ylabel 'Time (seconds)'
    
    # Get unique sizes for this dataset
    sizes = system(sprintf("awk '$1==\"%s\" {print $3}' timing_data.dat | sort -n | uniq", dataset))
    n_sizes = words(sizes)
    
    set datafile missing "NaN"
    # Create a plot with a line for each strategy
    plot for [j=1:n_strategies] \
            'timing_data.dat' using (strcol(1) eq dataset && strcol(2) eq word(strategies, j) ? $3 : NaN):4 \
            title word(strategies, j) \
            with linespoints ls j
}
EOF

# Run gnuplot
gnuplot plot.gnu

# Clean up temporary files
rm -f $TEMP_DATA plot.gnu