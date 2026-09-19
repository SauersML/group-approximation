#!/bin/bash
# exact wall test: enumerate canonical single-cycle (J=0) classes of H(e) at level B with glift, then decide by SAT
# whether any of them extends to level K.  "extendable 0" proves there is no single-cycle model at level K.
# usage: exact.sh e=n1,n2,n3,n4 B K [R]
cd $(dirname $0)
E=$1; B=$2; K=$3; R=${4:-noR}
./glift 0 $B $R $E dump 2>/dev/null | grep '^M' > /tmp/claude-0/-home-user-group-approximation/cfda3a9f-8576-509e-963c-f9b8ce875a39/scratchpad/swarm2/w19-053/bases-$E-$B.txt
python3 satlift.py 0 $K $E $R < /tmp/claude-0/-home-user-group-approximation/cfda3a9f-8576-509e-963c-f9b8ce875a39/scratchpad/swarm2/w19-053/bases-$E-$B.txt | grep -v '^model'
