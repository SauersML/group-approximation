#!/usr/bin/env bash
# List lane files not on origin/main (NEW) or differing from it (DIFF), for landable paths only.
GQ=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq
cd /Users/user/nonsofic_existence || exit 2
git ls-tree -r origin/main --format='%(objectname) %(path)' > $GQ/state/main-blobs.txt
: > $GQ/state/unlanded2.tsv
for d in $GQ/work/*/; do
  lane=$(basename "$d")
  ( cd "$d" && find GroupApproximation Palomar research scripts -type f \( -name '*.lean' -o -name '*.md' -o -name '*.json' \) 2>/dev/null; ls GroupApproximation.lean formalization.yaml 2>/dev/null ) | while read -r p; do
    case "$p" in
      GroupApproximation/*.lean|GroupApproximation.lean|Palomar/*|scripts/PalomarBooneHigman*.lean|formalization.yaml) kind=lean;;
      research/artifacts/gq-*.md) kind=res;;
      research/*/*) continue;;
      research/*.md) kind=res;;
      *) continue;;
    esac
    h=$(git hash-object "$d$p")
    m=$(grep -F " $p" $GQ/state/main-blobs.txt | awk -v p="$p" '$2==p{print $1}')
    if [ -z "$m" ]; then st=NEW; elif [ "$m" = "$h" ]; then continue; else st=DIFF; fi
    printf '%s\t%s\t%s\t%s\t%s\n' "$st" "$kind" "$lane" "$p" "$(stat -f %Sm -t '%m-%d %H:%M' "$d$p")" >> $GQ/state/unlanded2.tsv
  done
done
awk -F'\t' '{c[$1" "$2]++} END{for(k in c) print k, c[k]}' $GQ/state/unlanded2.tsv
echo; awk -F'\t' '$1=="NEW"{c[$3]++} END{for(k in c) print c[k], k}' $GQ/state/unlanded2.tsv | sort -rn | head -30
