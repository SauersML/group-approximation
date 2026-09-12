#!/usr/bin/env bash
# relaunch2.sh (acn112): stop the slow real-copy clone workers (pkgfix, lixclone v1) and start lixclone2.
set -u
P=/projects/standard/__MSI_GROUP__/__MSI_USER__
for pat in "xargs -P 4 -I" "xargs -P 6 -I" "fix_one nm-" "mk_one lix-" "bash pkgfix.sh" "lixclone.sh cs-endpoint"; do pkill -u __MSI_USER__ -f "$pat"; done
sleep 2
for pat in "rsync -a --delete --exclude /CharClass/" "rsync -a --exclude /.lake --exclude /.nm" "rsync -a --link-dest=$P/cc_clones/cs-endpoint" "rsync -a --exclude /.lake/build --exclude /.lake/packages" "rsync -a --link-dest=$P/cc_clones/lead"; do pkill -u __MSI_USER__ -f "$pat"; done
sleep 3
echo "remaining workers: $(ps -u __MSI_USER__ -o args | grep -E 'fix_one|mk_one|rsync -a ' | grep -vc grep)"
cd $P/nm
setsid nohup nice -n 10 bash $P/nm/lixclone2.sh cs-endpoint lix-a lix-b lix-c lix-d lix-e lix-f lix-g lix-h lix-i lix-j lix-k lix-l > $P/nm/lixclone2-lix.out 2>&1 < /dev/null &
setsid nohup nice -n 10 bash $P/nm/lixclone2.sh lead nm-a nm-b nm-c nm-d nm-e nm-f nm-g nm-h > $P/nm/lixclone2-nm.out 2>&1 < /dev/null &
sleep 2; head -1 $P/nm/lixclone2-lix.out $P/nm/lixclone2-nm.out
