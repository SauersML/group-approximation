#!/usr/bin/env bash
# palomar-verify.sh        (rescue-lix) one MSI job verifying the pending LIX-strong Palomar surface
# Overlay = local lakefile.toml, Palomar/LIXStrongChallenge.lean, scripts/check_palomar_statement_match.sh,
# scripts/check_palomar_submission.py over origin/main (current).  SLURM 16 cpus via dispatch.sh.
set -uo pipefail
NM=/private/tmp/claude-501/-Users-user-nonsofic-existence/77122910-de5a-4e59-a488-7cea550292c5/scratchpad/nm
REPO=/Users/user/nonsofic_existence
MSI=/Users/user/msi-node/msi; SOCK=/tmp/msi-login.sock; ALIAS=__MSI_LOGIN__
P=/projects/standard/__MSI_GROUP__/__MSI_USER__; CLONE=$P/cc_clones/cs-endpoint
TAG=$(date +%m%d-%H%M%S)-$$
cd "$REPO" || exit 2
git fetch -q origin main || exit 4
SHA=$(git rev-parse origin/main)
OVL=$NM/ov/palomar-$TAG; mkdir -p "$OVL/Palomar" "$OVL/scripts"
cp lakefile.toml "$OVL/lakefile.toml"
cp Palomar/LIXStrongChallenge.lean "$OVL/Palomar/"
cp scripts/check_palomar_statement_match.sh scripts/check_palomar_submission.py "$OVL/scripts/"
md5 -q lakefile.toml Palomar/LIXStrongChallenge.lean scripts/check_palomar_statement_match.sh scripts/check_palomar_submission.py > "$OVL.md5"
RSH="ssh -S $SOCK -o HostKeyAlias=$ALIAS -o LogLevel=ERROR"
"$MSI" true >/dev/null 2>&1 || "$MSI" up >/dev/null 2>&1 || { echo "PALOMAR VERIFY FAILED: msi down (infra)"; exit 4; }
rsync -rlc -e "$RSH" --rsync-path="mkdir -p $CLONE/.nm/pal-$TAG && rsync" "$OVL/" "$ALIAS:$CLONE/.nm/pal-$TAG/" || { echo "PALOMAR VERIFY FAILED: overlay upload (infra)"; exit 4; }
sed -e "s|__CLONE__|$CLONE|" -e "s|__TAG__|$TAG|" -e "s|__SHA__|$SHA|" "$NM/remote/palomar-verify.template.sh" > "$OVL.job.sh"
rsync -lc -e "$RSH" "$OVL.job.sh" "$ALIAS:$CLONE/.nm/paljob-$TAG.sh" || { echo "PALOMAR VERIFY FAILED: job upload (infra)"; exit 4; }
echo "palomar verify tag=$TAG base=${SHA:0:9}"
"$MSI" "bash $P/nm/dispatch.sh $CLONE/.nm/paljob-$TAG.sh $CLONE/.nm/palout-$TAG.txt nm-rescue-palomar 16" 2>&1
echo "overlay md5 as verified: $(tr '\n' ' ' < "$OVL.md5")"
