#!/bin/bash
#SBATCH --job-name=p13-hodge-lean
#SBATCH --time=01:00:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=32G
#SBATCH --output=literal-p13-hodge-build-%j.log

set -euo pipefail

if [ "$#" -ne 2 ]; then
  echo "usage: sbatch literal_p13_hodge_build.sbatch REPOSITORY_ROOT LAKE_BINARY" >&2
  exit 2
fi

cd "$1"
"$2" build \
  GroupApproximation.Sofic.LiteralP13HodgeCertificate
