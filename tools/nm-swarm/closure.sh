#!/bin/bash
# closure.sh <Module> : transitive GroupApproximation imports at origin/main (bash 3.2)
seen=$'\n'; q="$1"
while [ -n "$q" ]; do
  m=${q%% *}; if [ "$m" = "$q" ]; then q=""; else q=${q#* }; fi
  case "$seen" in *$'\n'"$m"$'\n'*) continue;; esac
  seen="$seen$m"$'\n'
  f=$(echo "$m" | tr . /).lean
  for i in $(git show origin/main:"$f" 2>/dev/null | grep -E '^import GroupApproximation' | awk '{print $2}'); do
    case "$seen" in *$'\n'"$i"$'\n'*) ;; *) q="$q $i"; q=${q# };; esac
  done
done
printf '%s' "$seen" | sed '/^$/d'
