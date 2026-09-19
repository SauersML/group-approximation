#!/usr/bin/env bash
W=$1
# name -> prop-constant binders
awk '{
  name=$0; sub(/^(protected |private |noncomputable )?(theorem|lemma) +/,"",name); sub(/[ ({:].*/,"",name); n=split(name,p,"."); short=p[n];
  s=$0; out="";
  while (match(s, /\(h[A-Za-z0-9_]* *: *[A-Z][A-Za-z0-9_.]*(\.\{[^}]*\})? *\)/)) { b=substr(s,RSTART,RLENGTH); out=out " " b; s=substr(s,RSTART+RLENGTH) }
  if (out!="") print short "\t" out
}' "$W/allsigs.txt" | sort -u -k1,1 > "$W/propbinders.tsv"
join -t $'\t' <(sort -u "$W/decls.txt") "$W/propbinders.tsv" > "$W/hits2.tsv"
