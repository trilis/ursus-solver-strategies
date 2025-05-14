JOBS=40
PROOF_JOBS=30
dune cle
./clear_gen.sh
(dune b --no-buffer -j $JOBS; dune b --no-buffer -j $JOBS; dune b --no-buffer -j $JOBS; dune b --no-buffer -j $JOBS; dune b --no-buffer -j $JOBS; dune b --no-buffer -j $PROOF_JOBS) &> plots/output.txt
cd plots
./plot.sh output.txt basic.txt 10
./plot.sh output.txt topdown.txt 10
./plot.sh output.txt native.txt 10
./plot.sh output.txt winners.txt 10
./plot.sh output.txt bottomup_naive.txt 10
./plot.sh output.txt bottomup_reductions.txt 10
./plot.sh output.txt winners.txt
cd ..