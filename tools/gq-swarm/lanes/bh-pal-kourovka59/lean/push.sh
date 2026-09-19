#!/bin/bash
# push.sh M1 M2 ... : upload modules then compile them in order on MSI
W=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq/work/bh-pal-kourovka59/lean
R=/projects/standard/hsiehph/sauer354/k1759
MSI=/Users/user/msi-node/msi
$MSI "mkdir -p $R/src/GroupApproximation/Kourovka1759" >/dev/null
$MSI put $W/k59.sh $R/k59.sh >/dev/null
for m in "$@"; do $MSI put $W/GroupApproximation/Kourovka1759/$m.lean $R/src/GroupApproximation/Kourovka1759/$m.lean >/dev/null || { echo PUT_FAIL $m; exit 1; }; done
$MSI "bash $R/k59.sh $*"
