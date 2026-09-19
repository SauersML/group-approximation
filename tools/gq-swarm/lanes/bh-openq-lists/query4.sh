#!/bin/bash
cd /projects/standard/hsiehph/sauer354/gqsrc/bh-openq; mkdir -p hunt4; cd hunt4; rm -f all.xml
for q in 'abs:%22simple+group%22' 'abs:%22piecewise+linear%22' 'abs:rearrangement' 'abs:%22cloning+system%22' 'abs:%22Higman-Thompson%22' 'abs:%22full+group%22' 'abs:%22ample+group%22' 'abs:%22almost+automorphism%22' 'abs:%22diagram+group%22' 'abs:%22automaton+group%22' 'abs:%22left-orderable%22' 'abs:%22word+problem%22' 'abs:%22finitely+presented%22' 'abs:Neretin' 'abs:commensurator' 'abs:%22groups+of+homeomorphisms%22' 'abs:%22Cantor+set%22' 'abs:%22problem+session%22' 'abs:%22open+problems%22' 'abs:%22branch+group%22' 'abs:%22iterated+monodromy%22' 'abs:%22Grigorchuk%22' 'abs:%22oligomorphic%22' 'abs:%22highly+transitive%22'; do
  curl -s -m 60 "https://export.arxiv.org/api/query?search_query=cat:math.GR+AND+$q&sortBy=submittedDate&sortOrder=descending&max_results=120" >> all.xml; sleep 3
done
tr '\n' ' ' < all.xml | sed 's/<entry>/\n<entry>/g' | grep '^<entry>' | while IFS= read -r e; do
  id=$(echo "$e" | grep -o -E 'abs/[0-9.]+v' | head -1 | sed 's#abs/##; s#v$##')
  d=$(echo "$e" | grep -o -E '<published>[0-9-]+' | sed 's/<published>//')
  t=$(echo "$e" | grep -o -E '<title>[^<]*' | sed 's/<title>//' | tr -s ' ')
  echo "$id $d $t"
done | sort -u -k1,1 | awk '$2 >= "2025-01-01"' | sort -k2 -r > list4.txt
echo QDONE $(wc -l < list4.txt)
