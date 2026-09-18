#!/usr/bin/env bash
# gen.sh <W> <lo> <hi> <outfile> <title> : one attestation module for census rows with lo <= line <= hi
W=$1; LO=$2; HI=$3; OUT=$4; TITLE=$5
awk -F'\t' -v lo=$LO -v hi=$HI '$7=="formalized" && $2>=lo && $2<=hi' $W/rows-a.tsv > $W/rows.sel
# imports: modules of every decl in the selected rows
awk -F'\t' '{n=split($8,a," "); for(i=1;i<=n;i++) print a[i]}' $W/rows.sel | sort -u > $W/decls.sel
awk -F'\t' 'NR==FNR{m[$1]=$2; next} ($1 in m){print m[$1]}' $W/declinfo.tsv $W/decls.sel | sort -u > $W/mods.sel
NR=$(wc -l < $W/rows.sel | tr -d ' '); ND=$(wc -l < $W/decls.sel | tr -d ' ')
{
  sed 's/^/import /' $W/mods.sel
  echo "import GroupApproximation.Meta.AxiomGuard"
  echo
  echo "/-!"
  echo "# $TITLE"
  echo
  echo "Attestation of the \`formalized\` rows of \`metadata/SK_SENTENCE_CENSUS.tsv\` whose sentence starts at"
  echo "\`simple_kazhdan_sofic_group.tex\` l.${LO}–${HI} (census at manuscript commit 22cdba8c): $NR rows, $ND distinct"
  echo "declarations.  Every declaration a row lists is audited here, grouped under its row, so that one build of"
  echo "this module checks the axiom closure of the whole range at once."
  echo
  echo "* \`#audit_closed_axioms\` for theorems that take no input (the statement is a closed proposition);"
  echo "* \`#audit_axioms\` for everything else: theorems whose inputs are the printed hypotheses of their sentence,"
  echo "  definitions and structures."
  echo
  echo "Both fail the build on any axiom outside \`propext\`, \`Classical.choice\` and \`Quot.sound\`.  The signatures"
  echo "were read by hand, and no declaration here takes a \`…Statement\` or another owed proposition as an input."
  echo "A declaration listed by several rows is audited at its first row only."
  echo "-/"
  echo
  awk -F'\t' 'NR==FNR{form[$1]=($6==1?"#audit_closed_axioms":"#audit_axioms"); next}
    { s=$9; gsub(/[\r\n]/," ",s); if (length(s)>88) { s=substr(s,1,85); while (length(s)>0 && substr(s,length(s),1) !~ /[ -~]/) s=substr(s,1,length(s)-1); s=s "..." }; lab=($6==""?"":" (" $6 ")");
      printf "-- %s, tex l.%s–%s%s: %s\n", $1, $2, $3, lab, s
      n=split($8,a," "); k=0
      for(i=1;i<=n;i++) if (!(a[i] in done)) { done[a[i]]=1; print form[a[i]] " " a[i]; k++ }
      if (k<n) printf "-- (%d further declaration(s) of this row are audited above)\n", n-k
      print "" }' $W/declinfo.tsv $W/rows.sel
} > $OUT
echo "$OUT: $(wc -l < $OUT) lines, $NR rows, $ND decls, $(wc -l < $W/mods.sel) imports"
