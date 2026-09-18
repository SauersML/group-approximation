# usage: runner.sh logfile r1 r2 ...   (waits for "U r=<r>:" in U8.txt, then runs slack_shard over enough shards)
cd /tmp/claude-0/-home-user-group-approximation/cfda3a9f-8576-509e-963c-f9b8ce875a39/scratchpad/relax
log=$1; shift
for r in "$@"; do
  until grep -q "^exit=[0-9]* r=$r\$" U8.txt; do sleep 20; done
  u=$(grep "^U r=$r:" U8.txt | awk '{print NF-2}')
  ns=$(( (u*u + 1199) / 1200 )); [ $ns -lt 1 ] && ns=1
  echo "## r=$r |U|=$u shards=$ns start $(date +%T)" >> $log
  for s in $(seq 0 $((ns-1))); do nice -n 10 timeout 1200 ./slack_shard 8 $r U8.txt $s $ns >> $log 2>&1; echo "exit=$? r=$r shard=$s/$ns $(date +%T)" >> $log; done
done
echo "## done" >> $log
