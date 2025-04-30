#!/bin/bash

# Check if input file is provided
if [ $# -lt 1 ] || [ $# -gt 4 ]; then
    echo "Usage: $0 <input_file> [strategy_filter_file] [max_dataset_size] [linear_fit]"
    echo "  strategy_filter_file: Optional file containing one strategy name per line"
    echo "  max_dataset_size: Optional maximum dataset size to include in plots"
    echo "  linear_fit: Optional flag (1 or 0) to enable/disable linear fitting"
    exit 1
fi

INPUT_FILE=$1
STRATEGY_FILTER_FILE=$2
MAX_SIZE=$3
LINEAR_FIT=${4:-0}  # Default to 0 (no linear fit)

# Create a temporary directory for processed data
TEMP_DIR="tmp"
mkdir -p "$TEMP_DIR"

# Extract and process the timing data
grep -o "\[.*\] ran for .* secs" --text "$INPUT_FILE" | while read -r line; do
    # Extract dataset, strategy, size, and time
    dataset=$(echo "$line" | grep -o "\[[^]]*\]" | head -n1 | tr -d '[]')
    strategy=$(echo "$line" | grep -o "\[[^]]*\]" | head -n2 | tail -n1 | tr -d '[]')

    # Extract strategy base name by removing the last token after hyphen
    strategy_base=$(echo "$strategy" | sed 's/-[^-]*$//')

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
            echo "$size $time" >> "$TEMP_DIR/${dataset}_${strategy_base}.dat"
        fi
    else
        echo "$size $time" >> "$TEMP_DIR/${dataset}_${strategy_base}.dat"
    fi
done

# Create gnuplot script
cat > plot.gnu << EOF
set terminal pngcairo enhanced size 800,600
set grid

# Get unique datasets and strategies
datasets = system("ls $TEMP_DIR/*.dat | xargs -n1 basename | cut -d'_' -f1 | sort -u")
strategies = system("ls $TEMP_DIR/*.dat | xargs -n1 basename | cut -d'_' -f2 | cut -d'.' -f1 | sort -u")
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
    set output sprintf('%s%s%s.png', dataset, '${STRATEGY_FILTER_FILE:+_$(basename "$STRATEGY_FILTER_FILE" .txt)}', '${MAX_SIZE:+_max${MAX_SIZE}}')
    set xlabel 'Dataset Size'
    set ylabel 'Time (seconds)'
    set title dataset
    
    set datafile missing "NaN"
    #set key top left
    
    # Create a plot with a line for each strategy
    if ($LINEAR_FIT == 1) {
        # First perform linear fits for each strategy
        f1(x) = a1 * x * x + b1 * x + c1
        f2(x) = a2 * x * x + b2 * x + c2
        f3(x) = a3 * x * x + b3 * x + c3
        f4(x) = a4 * x + b4
        f5(x) = a5 * x + b5
        f6(x) = a6 * x + b6
        f7(x) = a7 * x + b7
        f8(x) = a8 * x + b8
        f9(x) = a9 * x + b9
        f10(x) = a10 * x + b10
        g(i,x) = \
        i == 1 ? f1(x) : \
        i == 2 ? f2(x) : \
        i == 3 ? f3(x) : \
        i == 4 ? f4(x) : \
        i == 5 ? f5(x) : \
        i == 6 ? f6(x) : \
        i == 7 ? f7(x) : \
        i == 8 ? f8(x) : \
        i == 9 ? f9(x) : \
        i == 10 ? f10(x) : \
        NaN
        fit g(1, x) '$TEMP_DIR/'.dataset.'_'.word(strategies, 1).'.dat' using 1:2 via a1, b1, c1
        fit g(2, x) '$TEMP_DIR/'.dataset.'_'.word(strategies, 2).'.dat' using 1:2 via a2, b2, c2
        fit g(3, x) '$TEMP_DIR/'.dataset.'_'.word(strategies, 3).'.dat' using 1:2 via a3, b3, c3
        
        # Plot data points and fitted lines
        plot for [j=1:n_strategies] \
                '$TEMP_DIR/'.dataset.'_'.word(strategies, j).'.dat' using 1:2 \
                title word(strategies, j) \
                with linespoints ls j, \
                for [j=1:n_strategies] \
                g(j, x) \
                notitle with lines ls j lw 2
    } else {
        # Plot only data points without fits
        plot for [j=1:n_strategies] \
                '$TEMP_DIR/'.dataset.'_'.word(strategies, j).'.dat' using 1:2 \
                title word(strategies, j) \
                with linespoints ls j
    }
}
EOF

# Run gnuplot
gnuplot plot.gnu

# Clean up temporary files
rm -rf $TEMP_DIR plot.gnu