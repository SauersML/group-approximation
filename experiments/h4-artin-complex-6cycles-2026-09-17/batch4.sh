# H4 single-edge (pure) configurations: a,c in PureBall_Y(2), b in PureBall_X(2), u in R_X(1), rescan R_X(2); K=4, K2=5
for i in $(seq 0 68); do
  A0=$i A1=$((i+1)) nice -n 10 timeout 1200 ./tsearch data/PH4_22212 4 5 2>>batch4.err >> PH4_22212.out
  echo "chunk $i exit $?" >> batch4.err
done
