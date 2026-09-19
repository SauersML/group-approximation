# H4 LA=3 LB=4 split by F-element index (4 chunks of the 187-element F-ball), then exact pairing.
cd "$(dirname "$0")"
while pgrep -f 'cchelly (A4|B4|H4r)' >/dev/null; do sleep 20; done
for c in 0 1 2 3; do
  f0=$((c*47)); f1=$((f0+47))
  ( time nice -n 10 timeout 1200 ./cchelly h4 3 4 hash $f0 $f1 /tmp/claude-0/-home-user-group-approximation/cfda3a9f-8576-509e-963c-f9b8ce875a39/scratchpad/w14tmp/c34_$c.bin ) >> C34.log 2>&1 || echo "chunk $c FAILED" >> C34.log
done
( time nice -n 10 timeout 1200 ./cchelly h4 3 4 pair /tmp/claude-0/-home-user-group-approximation/cfda3a9f-8576-509e-963c-f9b8ce875a39/scratchpad/w14tmp/c34_0.bin /tmp/claude-0/-home-user-group-approximation/cfda3a9f-8576-509e-963c-f9b8ce875a39/scratchpad/w14tmp/c34_1.bin /tmp/claude-0/-home-user-group-approximation/cfda3a9f-8576-509e-963c-f9b8ce875a39/scratchpad/w14tmp/c34_2.bin /tmp/claude-0/-home-user-group-approximation/cfda3a9f-8576-509e-963c-f9b8ce875a39/scratchpad/w14tmp/c34_3.bin ) >> C34.log 2>&1
rm -f /tmp/claude-0/-home-user-group-approximation/cfda3a9f-8576-509e-963c-f9b8ce875a39/scratchpad/w14tmp/c34_?.bin
grep RESULT C34.log || tail -5 C34.log
