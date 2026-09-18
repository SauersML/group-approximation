cd /projects/standard/hsiehph/sauer354/openq-lists/ksrc
LC_ALL=C awk -v P1="$1" -v P2="$2" -v P3="$3" -v W="${4:-900}" '
function flush(){ if (blk!="") { gsub(/[ \t\n]+/," ",blk); b=tolower(blk); if (b ~ P1 && b ~ P2 && b ~ P3) { print "@@ " start ": " substr(blk,1,W) "\n" } } }
/\\textbf\{(\\zv )?[0-9]+\.[0-9]+[a-z]?\.\}/ { flush(); blk=$0; start=NR; next }
{ blk = blk " " $0 }
END { flush() }' 21tkt.tex
