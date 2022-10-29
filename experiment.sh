#!/bin/bash
alpha="0.04"
for dir in data/S-*; do 
echo "Result, IterSP, restarts, nAssignedVarsSP, nAssignedVarsVSID, cpuTime, cpuTimeSP, cpuTimeG, backtracks, backtracksBefore, convsAfterLevel, convsBeforeLevel" > ${dir}/result_${alpha}.csv
	for file in $dir/*.txt; do
		echo $file
		./simp/glucose -no-elim -cpu-lim=600 $file result ${dir}/result_${alpha}.csv
	done
done

#for dir in data/S-*; do
#	for i in {1..9}; do
#		mv ${dir}/cnf_$i.txt ${dir}/cnf_0$i.txt
#	done
#done
