#!/bin/bash
# For each fetched paper, print question/problem/conjecture environments and "open" sentences with TeX line numbers.
cd /projects/standard/hsiehph/sauer354/gqsrc/bh-openq/hunt2
out=extract2.txt; : > $out
for d in src_*; do
  id=${d#src_}
  files=$(find $d -name '*.tex' 2>/dev/null)
  [ -z "$files" ] && { echo "##### $id NO-TEX" >> $out; continue; }
  echo "##### $id" >> $out
  for f in $files; do
    LC_ALL=C awk -v F="${f#$d/}" '
      /\\begin\{(question|problem|conjecture|qu|ques|quest|prob|conj|openquestion|openproblem)\*?\}/ {inq=1; buf=""; start=NR}
      inq {buf=buf" "$0}
      inq && /\\end\{(question|problem|conjecture|qu|ques|quest|prob|conj|openquestion|openproblem)\*?\}/ {inq=0; gsub(/[ \t]+/," ",buf); print "[ENV " F ":" start "] " substr(buf,1,900)}
      !inq && tolower($0) ~ /(we do not know|remains open|remain open|is open|still open|natural to ask|would be interesting|we ask|open question|open problem|unknown whether|not known whether|do not know whether|we wonder|it is unclear)/ {line=$0; gsub(/[ \t]+/," ",line); print "[TXT " F ":" NR "] " substr(line,1,400)}
    ' "$f" >> $out
  done
done
echo EXTRACTDONE $(wc -l < $out)
