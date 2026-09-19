#!/usr/bin/env bash
GQ=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq
cd /Users/user/nonsofic_existence
land() { # lane subject paths...
  local lane=$1 subj=$2; shift 2
  local m=$GQ/msgs/restart-$lane.txt
  printf '%s\n\nLanded by the coordinator after a restart stopped lane %s before it could land this draft. The text is the lane'"'"'s own, unchanged.\n' "$subj" "$lane" > "$m"
  echo "### $lane"; timeout 900 bash $GQ/gqland.sh "$lane" "$m" "$@" 2>&1 | tail -3
}
land bh-groupoid "Kazhdan simple groups with no finite quotients act trivially on trees and Bruhat-Tits buildings" research/kazhdan-simple-groups-act-only-on-exotic-2d-buildings.md
land bh-invent-02 "Amalgams of orbit-finite actions along a common subgroup are type A_2" research/amalgams-of-orbit-finite-actions-are-type-a2.md
land bh-major-cube-b "Pointed-cube categories of free cocompact cubulations are Garside categories in Li's sense" research/pointed-cube-categories-are-li-garside-categories.md research/pointed-cube-categories-li-garside-proof.md
land bh-major-onerel "Finite germ extensions of V with two singular rational orbits contain Baumslag-Solitar chain configurations" research/bs-chain-configurations-exist-in-finite-germ-extensions-of-v.md
land bh-major-product "Unit groups of L_p tensor L_p lie in the permutational class for every prime p" research/leavitt-tensor-unit-groups-lie-in-the-permutational-class.md
land bh-solvable "Hall's quotient B/C embeds neither in V nor in circle homeomorphism groups" research/hall-quotient-avoids-v-circle-groups-and-periodic-ends.md
