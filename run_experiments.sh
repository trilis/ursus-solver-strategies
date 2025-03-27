dune cle
./clear_gen.sh
(dune b --no-buffer; dune b --no-buffer; dune b --no-buffer; dune b --no-buffer; dune b --no-buffer; dune b --no-buffer) &> output.txt
./plot.sh output.txt