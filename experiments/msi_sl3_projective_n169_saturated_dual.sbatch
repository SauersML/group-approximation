#!/bin/bash
#SBATCH --job-name=n169-sat-dual
#SBATCH --time=12:00:00
#SBATCH --mem=64G
#SBATCH --cpus-per-task=1

set -euo pipefail

if [ "$#" -ne 1 ]; then
    echo "usage: sbatch msi_sl3_projective_n169_saturated_dual.sbatch PROJECT_HOME" >&2
    exit 2
fi

PROJECTIVE_HOME="$1"
TOOLS_DIR="$PROJECTIVE_HOME/research-tools"

module load sagemath/10.7
export DOT_SAGE="$PROJECTIVE_HOME/.sage"
cd "$TOOLS_DIR"

sage -python sl3_projective_dual_packet_sparse.py \
    projective-cellular-n169.tsv \
    projective-cellular-n169-cycle-boundary-saturated.json \
    projective-cellular-n169-dual-packet-saturated-lll.json \
    --time-limit 3600 \
    --finish-residual-hnf \
    --greedy-sweeps 20 \
    --saturation-direction-certificate \
      projective-cellular-n169-d2-saturation-p13.json \
    --lll-saturated-reduce \
    > projective-cellular-n169-dual-packet-saturated-lll.log 2>&1

touch projective-cellular-n169-dual-packet-saturated-lll.done
