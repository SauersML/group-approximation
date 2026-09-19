#!/usr/bin/env bash
GQ=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq
E=$GQ/work/bh-pal-integrate/scratch/errindex-3c8b417428.txt
W=$GQ/work/fix-bh-a; mkdir -p $W/research
: > $W/paths.txt; : > $W/fixgraph-lines.txt
while IFS=$'\t' read -r rel n wire ch first; do
  p=GroupApproximation/BooneHigman/Metabelian/$rel
  mod=GroupApproximation.BooneHigman.Metabelian.$(echo "${rel%.lean}" | tr / .)
  slug=$(echo "${rel%.lean}" | perl -pe 's/([a-z0-9])([A-Z])/$1-$2/g; s/([A-Z])([A-Z][a-z])/$1-$2/g; $_=lc; s|/|-|g')
  id=fix-bh-met-$slug
  [ ${#id} -le 64 ] || { echo "TOO LONG $id"; continue; }
  kind="proof error"
  echo "$first" | grep -qE 'noncomputable|automatically included section|Unknown constant|expected token|unexpected token' && kind="mechanical (Lean/Mathlib drift)"
  errs=$(grep -F "$p:" $E | head -3 | sed "s|^error: $p:|    line |" | cut -c1-160)
  cat > $W/research/$id.md <<NODE
---
id: $id
kind: route
rg: 2
title: "Fix $mod: $(echo "$first" | sed 's/^[0-9]*:[0-9]*: //; s/"//g' | cut -c1-70) ($n errors on main 3c8b417428)"
target: fp-metabelian-groups-satisfy-boone-higman
status: OPEN
---

**Module.** \`$p\`. It is red on origin/main at 3c8b417428 with $n hard errors, from bh-pal-integrate's trusted MSI build
(error index \`work/bh-pal-integrate/scratch/errindex-3c8b417428.txt\`). The file is unchanged on main since then.
It sits in the closure of the metabelian chain (\`Metabelian/ChainWiredFrontierThree\`, route A
\`bhNagaoUncond_fpMetabelian_routeA\`), so while it is red, T2/T3 cannot build.

**First errors.**
\`\`\`
$errs
\`\`\`

**Kind.** $kind.

**Owner and repair.** Lane \`bh-pal-wire\` owns the BooneHigman/Metabelian repairs (LEAN-OWNERS). Its repair of this file is
written but not yet probed: noncomputable sections, \`omit … in\`, missing Mathlib imports, renamed lemmas, and the proof
fixes listed on its board. The repair is waiting in the serialized MSI probe queue.

**Resolve when.** A trusted build (\`gqprobe-lean.sh\`) of \`$mod\` is green with no errors, and the repaired bytes are on
main. Then flip \`status\` to RESOLVED and cite the green commit.
NODE
  echo "research/$id.md" >> $W/paths.txt
  echo "OPEN $id $p bh-pal-wire" >> $W/fixgraph-lines.txt
done < $GQ/state/bh-red-27.tsv
wc -l < $W/paths.txt; head -2 $W/fixgraph-lines.txt; awk 'length($2)>60' $W/fixgraph-lines.txt | head
