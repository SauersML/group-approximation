#!/usr/bin/env bash
W=$1; cd /Users/user/nonsofic_existence; : > $W/declinfo.tsv
while IFS=$'\t' read -r full mod ln; do f=$(printf '%s' "$mod" | tr . /).lean
  git show "refs/remotes/origin/main:$f" > $W/cur.lean
  first=$(sed -n "${ln}p" $W/cur.lean)
  priv=0; printf '%s\n' "$first" | grep -qE '^(@\[[^]]*\] *)?private ' && priv=1
  kw=$(printf '%s\n' "$first" | awk '{for(i=1;i<=NF;i++) if ($i ~ /^(theorem|lemma|def|abbrev|instance|structure|class|inductive)$/) {print $i; exit}}')
  var=$(awk -v L=$ln 'NR>=L{exit} /^ *variable[ ({\[]/{v++} END{print v+0}' $W/cur.lean)
  sig=$(awk -v L=$ln 'NR>=L && NR<L+40 {printf "%s ", $0; if ($0 ~ /:=/ || $0 ~ /[ ]where( |$)/) exit}' $W/cur.lean)
  closed=0
  if printf '%s\n' "$sig" | grep -qE "^ *(@\[[^]]*\] *)?(private |protected |noncomputable )*(theorem|lemma) [^ ]+ *: " && ! printf '%s\n' "$sig" | grep -qE '→|∀' && [ "$var" = 0 ]; then closed=1; fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$full" "$mod" "$kw" "$priv" "$var" "$closed" >> $W/declinfo.tsv
done < $W/res-mod.tsv
