for f in ps_*.ms; do
  o=${f%.ms}.out
  [ -s $o ] || nice -n 10 timeout 1200 msolve -t 1 -f $f -o $o >/dev/null 2>&1 || echo "FAIL $f" >> fails.txt
done
echo DONE > done.txt
