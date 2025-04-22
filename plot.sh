#!/bin/bash

# Check if input file is provided
if [ $# -lt 1 ] || [ $# -gt 3 ]; then
    echo "Usage: $0 <input_file> [strategy_filter_file] [max_dataset_size]"
    echo "  strategy_filter_file: Optional file containing one strategy name per line"
    echo "  max_dataset_size: Optional maximum dataset size to include in plots"
    exit 1
fi

INPUT_FILE=$1
STRATEGY_FILTER_FILE=$2
MAX_SIZE=$3

# Create a temporary file for processed data
TEMP_DATA="timing_data.dat"

# Extract and process the timing data
grep -o "\[.*\] ran for .* secs" "$INPUT_FILE" | while read -r line; do
    # Extract dataset, strategy, size, and time
    dataset=$(echo "$line" | grep -o "\[[^]]*\]" | head -n1 | tr -d '[]')
    strategy=$(echo "$line" | grep -o "\[[^]]*\]" | head -n2 | tail -n1 | tr -d '[]')
    size=$(echo "$line" | grep -o "\[[^]]*\]" | tail -n1 | tr -d '[]')
    time=$(echo "$line" | grep -o "ran for [0-9.]*" | cut -d' ' -f3)
    
    # If max size is provided, check if this data point should be included
    if [ -n "$MAX_SIZE" ]; then
        if [ "$size" -gt "$MAX_SIZE" ]; then
            continue
        fi
    fi
    
    # If strategy filter file is provided, only include matching strategies
    if [ -n "$STRATEGY_FILTER_FILE" ]; then
        if grep -q "^${strategy}$" "$STRATEGY_FILTER_FILE"; then
            echo "$dataset $strategy $size $time" >> $TEMP_DATA
        fi
    else
        echo "$dataset $strategy $size $time" >> $TEMP_DATA
    fi
done

# Create gnuplot script
cat > plot.gnu << EOF
set terminal pngcairo enhanced size 800,600
set grid

# Get unique datasets and strategies
datasets = system("awk '{print \$1}' timing_data.dat | sort -u")
strategies = system("awk '{print \$2}' timing_data.dat | sort -u")
n_datasets = words(datasets)
n_strategies = words(strategies)

# Set line styles with 10 distinct colors
set style line 1 lc rgb '#1f77b4' lt 1 lw 1 pt 7 ps 1.5  # blue
set style line 2 lc rgb '#d62728' lt 1 lw 1 pt 7 ps 1.5  # red
set style line 3 lc rgb '#2ca02c' lt 1 lw 1 pt 7 ps 1.5  # green
set style line 4 lc rgb '#9467bd' lt 1 lw 1 pt 7 ps 1.5  # purple
set style line 5 lc rgb '#ff7f0e' lt 1 lw 1 pt 7 ps 1.5  # orange
set style line 6 lc rgb '#8c564b' lt 1 lw 1 pt 7 ps 1.5  # brown
set style line 7 lc rgb '#e377c2' lt 1 lw 1 pt 7 ps 1.5  # pink
set style line 8 lc rgb '#7f7f7f' lt 1 lw 1 pt 7 ps 1.5  # gray
set style line 9 lc rgb '#bcbd22' lt 1 lw 1 pt 7 ps 1.5  # yellow-green
set style line 10 lc rgb '#17becf' lt 1 lw 1 pt 7 ps 1.5 # cyan

# Create a plot for each dataset
do for [i=1:n_datasets] {
    dataset = word(datasets, i)
    # Check if there's data for this dataset
    set output sprintf('%s%s%s.png', dataset, '${STRATEGY_FILTER_FILE:+_$(basename "$STRATEGY_FILTER_FILE" .txt)}', '${MAX_SIZE:+_max${MAX_SIZE}}')
    set xlabel 'Dataset Size'
    set ylabel 'Time (seconds)'
    
    # Get unique sizes for this dataset
    sizes = system(sprintf("awk '\$1==\"%s\" {print \$3}' timing_data.dat | sort -n | uniq", dataset))
    n_sizes = words(sizes)
    
    set datafile missing "NaN"
    # Create a plot with a line for each strategy
    plot for [j=1:n_strategies] \
            'timing_data.dat' using (strcol(1) eq dataset && strcol(2) eq word(strategies, j) ? \$3 : NaN):4 \
            title word(strategies, j) \
            with linespoints ls j
}
EOF

# Run gnuplot
gnuplot plot.gnu

# Clean up temporary files
rm -f $TEMP_DATA plot.gnu