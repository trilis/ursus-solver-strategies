dune cle
./clear_gen.sh
(dune b --no-buffer; dune b --no-buffer; dune b --no-buffer; dune b --no-buffer; dune b --no-buffer; dune b --no-buffer) &> plots/output.txt
cd plots
./plot.sh output.txt basic.txt
./plot.sh output.txt topdown.txt
./plot.sh output.txt native.txt
./plot.sh output.txt winners.txt
./plot.sh output.txt bottomup_naive.txt
./plot.sh output.txt bottomup_reductions.txt
cd ..