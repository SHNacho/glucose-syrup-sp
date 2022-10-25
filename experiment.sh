#!/bin/bash
echo "" > results.txt
for file in data/S-4.21/*.txt; do
	./simp/glucose -no-elim -cpu-lim=600 $file
done
