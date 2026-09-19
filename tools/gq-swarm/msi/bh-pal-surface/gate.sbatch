#!/bin/bash
#SBATCH -p msismall
#SBATCH -c 1
#SBATCH --mem=4G
#SBATCH --time=00:20:00
#SBATCH -J gq-bh-pal-surface-gate
#SBATCH --output=/projects/standard/hsiehph/sauer354/bh-pal-surface/gate-%j.out
set -u
cd /projects/standard/hsiehph/sauer354/bh-pal-surface || exit 3
PY=""
for c in /usr/bin/python3.11 /usr/bin/python3.12 /usr/bin/python3.9 $(ls -d /common/software/install/*/*/python*/bin/python3 /projects/standard/hsiehph/sauer354/*/bin/python3 2>/dev/null); do
  [ -x "$c" ] || continue
  if "$c" -c 'import sys, yaml; assert sys.version_info >= (3, 9)' 2>/dev/null; then PY=$c; break; fi
done
[ -z "$PY" ] && for c in /usr/bin/python3.11 /usr/bin/python3.12; do [ -x "$c" ] && PY=$c && break; done
echo "python: $PY $($PY --version 2>&1); yaml: $($PY -c 'import yaml; print(yaml.__version__)' 2>&1 | tail -1)"
rm -rf gatetree && mkdir gatetree && tar -xzf gatetree.tgz -C gatetree || exit 4
cd gatetree
git init -q . && git add -A && git -c user.name=gate -c user.email=gate@localhost commit -qm gate
echo "===== GATE"
$PY scripts/check_palomar_submission.py; echo "===== GATE RC $?"
echo "===== SELFTEST"
$PY scripts/check_palomar_submission.py --self-test 2>&1 | tail -40; echo "===== SELFTEST RC ${PIPESTATUS[0]}"
