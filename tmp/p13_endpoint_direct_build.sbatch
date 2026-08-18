#!/usr/bin/env bash
#SBATCH --account=hsiehph
#SBATCH --partition=agsmall
#SBATCH --cpus-per-task=1
#SBATCH --mem=16G
#SBATCH --time=01:00:00
#SBATCH --output=/projects/standard/hsiehph/sauer354/p13_exact_isolated_20260813/endpoint-build-%j.log

set -euo pipefail
if [[ "$#" != 1 ]]; then
  echo "usage: p13_endpoint_direct_build.sbatch MODULE_STEM" >&2
  exit 2
fi
stem="$1"
if [[ ! "$stem" =~ ^(GroupApproximation(/[A-Za-z0-9_]+)*/[A-Za-z0-9_]+|GroupApproximation)$ ]]; then
  echo "invalid endpoint module stem: $stem" >&2
  exit 2
fi
export PATH=/projects/standard/hsiehph/sauer354/.elan/bin:$PATH
cd /projects/standard/hsiehph/sauer354/p13_exact_isolated_20260813/project
mkdir -p ".lake/build/lib/lean/$(dirname "$stem")"
lake env lean -DwarningAsError=true "${stem}.lean" \
  -o ".lake/build/lib/lean/${stem}.olean" \
  -i ".lake/build/lib/lean/${stem}.ilean"
