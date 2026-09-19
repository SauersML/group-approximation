#!/usr/bin/env bash
# closure of modules over a git tree: closure.sh <sha> <Module...>
B=$1; shift; cd /Users/user/nonsofic_existence
printf '%s\n' "$@" > /tmp/cl.fr.$$; : > /tmp/cl.seen.$$
while [ -s /tmp/cl.fr.$$ ]; do
  cat /tmp/cl.fr.$$ >> /tmp/cl.seen.$$; : > /tmp/cl.nx.$$
  while read -r m; do f="$(echo "$m" | tr . /).lean"; git show "$B:$f" 2>/dev/null | awk '/^import GroupApproximation/{print $2}' >> /tmp/cl.nx.$$; done < /tmp/cl.fr.$$
  sort -u /tmp/cl.nx.$$ | comm -23 - <(sort -u /tmp/cl.seen.$$) > /tmp/cl.fr.$$
done
sort -u /tmp/cl.seen.$$; rm -f /tmp/cl.*.$$
