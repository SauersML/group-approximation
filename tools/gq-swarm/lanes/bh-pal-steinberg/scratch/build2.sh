#!/bin/bash
W=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq/work/bh-pal-steinberg
while pgrep -f 'scripts/remote-build.sh' > /dev/null; do sleep 20; done
echo "no remote-build running $(date +%T)"
cd /Users/user/nonsofic_existence && git rev-parse --short HEAD && git status --short | head -3
MSI_BUILD_CORES=24 MSI_BUILD_TAG=bhpalst2 timeout 3000 bash scripts/remote-build.sh GroupApproximation.SteinbergFP.Challenge < /dev/null > $W/scratch/build2.out 2>&1
echo "rc=$? $(date +%T)"
