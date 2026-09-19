#!/bin/bash
# Lock-free check of the edited Palomar BH solution against the shared warm build (writes only private files).
W=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq/work/bh-pal-steinberg
PD=/projects/standard/hsiehph/sauer354/gqsrc/bh-pal-steinberg/palcheck
REMOTE=/projects/standard/hsiehph/sauer354/nonsofic_existence
MSI=/Users/user/msi-node/msi
timeout 60 $MSI "rm -rf $PD && mkdir -p $PD/src/Palomar $PD/olean/Palomar && echo SENTINEL_MK" < /dev/null | tail -1
timeout 60 $MSI put $W/Palomar/BooneHigmanSolution.lean $PD/src/Palomar/BooneHigmanSolution.lean < /dev/null > /dev/null || { echo PUTFAIL1; exit 1; }
timeout 60 $MSI put $W/scripts/PalomarBooneHigmanAxioms.lean $PD/src/PalomarBooneHigmanAxioms.lean < /dev/null > /dev/null || { echo PUTFAIL2; exit 1; }
timeout 1800 $MSI "cd $REMOTE && export PATH=\$HOME/.elan/bin:\$PATH LEAN_NUM_THREADS=4; md5sum $PD/src/Palomar/BooneHigmanSolution.lean $PD/src/PalomarBooneHigmanAxioms.lean; \
  timeout 1500 nice taskset -c 0-3 lake env lean -R $PD/src -o $PD/olean/Palomar/BooneHigmanSolution.olean -i $PD/olean/Palomar/BooneHigmanSolution.ilean $PD/src/Palomar/BooneHigmanSolution.lean > $PD/sol.log 2>&1; echo sol_rc=\$?; head -c 3000 $PD/sol.log; \
  timeout 600 nice taskset -c 0-3 lake env bash -c 'LEAN_PATH=$PD/olean:\$LEAN_PATH lean $PD/src/PalomarBooneHigmanAxioms.lean' > $PD/ax.log 2>&1; echo ax_rc=\$?; grep -E 'error|axiom closure|MISSING|sorry' $PD/ax.log | cut -c1-240 | head -30; echo SENTINEL_OK" < /dev/null 2>&1 | tail -60
