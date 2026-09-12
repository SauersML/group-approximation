#!/usr/bin/env bash
# USER ORDER 21:45 "dont do unnecessary msi compute": keep 4 LIX clones (lix-a..d), stop the rest.
P=/projects/standard/__MSI_GROUP__/__MSI_USER__
for c in lix-e lix-f lix-g lix-h nm-e nm-f nm-g nm-h; do pkill -u __MSI_USER__ -f "mk_one $c\$"; pkill -u __MSI_USER__ -f "cc_clones/$c/"; done
sleep 3
ps -u __MSI_USER__ -o args | grep -E 'mk_one|rsync -a' | grep -v grep | sed -E 's|.*cc_clones/([a-z0-9-]+)/.lake.*|\1|; s|bash -c mk_one ||' | sort | uniq -c
