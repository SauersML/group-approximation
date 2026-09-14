#!/usr/bin/env bash
# bcbase.sh <SHA> <Module...>   (runs ON MSI, detached with setsid nohup)
# Base warm build of the campaign import closure in the ONE campaign clone, through the shared nm dispatch
# (32 cpus -> SLURM msismall,amdsmall) with the shared Lake artifact cache; no overlay.
# Refuses before queueing a job when the SHA is not in the mirror or its tree lacks GroupApproximation.lean,
# lake-manifest.json or lakefile.toml; bcjob.template.sh repeats that check, and its sync guards, under the clone lock.
set -u
P=/projects/standard/__MSI_GROUP__/__MSI_USER__; BCR=$P/bc; CLONE=$P/bc_clones/bc; MIR=$P/nm/mirror.git
SHA=${1:?usage: bcbase.sh <SHA> <Module...>}; shift; MODS="$*"
[ -n "$MODS" ] || { echo "[bcbase] REFUSED: no modules"; exit 2; }
exec 8>"$P/nm/mirror.lock"; flock -w 900 8 || { echo "[bcbase] REFUSED: mirror lock busy"; exit 4; }
git -C "$MIR" fetch -q origin 2>/dev/null
exec 8>&-
git -C "$MIR" cat-file -e "$SHA^{commit}" 2>/dev/null || { echo "[bcbase] REFUSED: mirror lacks $SHA"; exit 4; }
for root in GroupApproximation.lean lake-manifest.json lakefile.toml; do
  git -C "$MIR" cat-file -e "$SHA:$root" 2>/dev/null || { echo "[bcbase] REFUSED: ${SHA:0:9} lacks $root (gutted tree)"; exit 4; }
done
TAG=base-$(date +%m%d-%H%M%S)
mkdir -p "$CLONE/.nm/ov-$TAG"
sed -e "s|__TAG__|$TAG|" -e "s|__SHA__|$SHA|" -e "s|__MODS__|$MODS|" -e "s|__LANE__|bc-infra|" \
  "$BCR/bcjob.template.sh" > "$CLONE/.nm/job-$TAG.sh"
echo "[bcbase] $(date +%T) tag=$TAG sha=${SHA:0:9} modules=$(echo $MODS | wc -w)"
T0=$(date +%s)
bash "$P/nm/dispatch.sh" "$CLONE/.nm/job-$TAG.sh" "$CLONE/.nm/out-$TAG.txt" bc-base "${BC_CPUS:-32}"; RC=$?
echo "BCBASE_DONE rc=$RC seconds=$(( $(date +%s) - T0 )) out=$CLONE/.nm/out-$TAG.txt"
