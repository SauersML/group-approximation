#!/usr/bin/env bash
W=$1; IN=$2; cd /Users/user/nonsofic_existence
: > $W/resolved2.tsv; : > $W/unresolved2.txt
while read -r full; do last=${full##*.}
  cands=$(awk -v L="$last" -F: '{s=$0; sub(/^[^:]*:[^:]*:[0-9]+:/,"",s); n=split(s,t,/[ \t(:{]+/); nm=""; for(i=1;i<=n;i++) if (t[i] ~ /^(theorem|lemma|def|abbrev|instance|structure|class|inductive)$/) {nm=t[i+1]; break}; m=split(nm,q,"."); if (q[m]==L) print $2":"$3}' $W/alldecls.txt | sort -u)
  found=""
  for c in $cands; do f=${c%%:*}; ln=${c##*:}
    ns=$(git show "origin/main:$f" | awk -v L=$ln 'NR>=L{exit} /^namespace /{st[++d]=$2} /^end /{ if(d>0 && $2==st[d]) d--} END{s=""; for(i=1;i<=d;i++) s=s (s==""?"":".") st[i]; print s}')
    dn=$(git show "origin/main:$f" | sed -n "${ln}p" | awk '{for(i=1;i<=NF;i++) if ($i ~ /^(theorem|lemma|def|abbrev|instance|structure|class|inductive)$/) {print $(i+1); exit}}')
    cand="${ns:+$ns.}$dn"
    if [ "$cand" = "$full" ] || [ "${dn#_root_.}" = "$full" ]; then found="$f:$ln"; break; fi
  done
  if [ -n "$found" ]; then printf '%s\t%s\n' "$full" "$found" >> $W/resolved2.tsv; else echo "$full" >> $W/unresolved2.txt; fi
done < $IN
