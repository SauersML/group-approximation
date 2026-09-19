#!/bin/sh
# Regenerates run_excision.txt.  Usage: sh run_all.sh > run_excision.txt
D=$(dirname "$0")
W1=$(python3 -c "print('0'*58+'1')")
W2=$(python3 -c "print('0'*150+'1'*4+'0'*70+'1')")
W3=$(python3 -c "print('1'*90+'0'+'1'*2+'0'*40+'1')")
python3 "$D/run_excision.py" "$W1" 1 4 6 1
python3 "$D/run_excision.py" "$W1" -1 6 6 2
python3 "$D/run_excision.py" "$W2" -1 10 8 2
python3 "$D/run_excision.py" "$W2" 0.6+0.8j 16 8 3
python3 "$D/run_excision.py" "$W3" 1j 6 6 2
