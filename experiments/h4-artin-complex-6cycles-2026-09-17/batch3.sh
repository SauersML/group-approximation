# H4 (La,Lb,Lc,Lu,Lu2)=(2,2,2,2,2), K=4, K2=5; one a-index per chunk (each under its own timeout)
for i in $(seq 0 35); do
  A0=$i A1=$((i+1)) nice -n 10 timeout 1200 ./tsearch data/H4_22222 4 5 2>>batch3.err >> H4_22222.out
  echo "chunk $i exit $?" >> batch3.err
done
