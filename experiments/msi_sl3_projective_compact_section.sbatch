#!/bin/bash
#SBATCH --job-name=sl3-compact-section
#SBATCH --time=08:00:00
#SBATCH --mem=32G
#SBATCH --cpus-per-task=1

set -euo pipefail

if [ "$#" -ne 2 ]; then
    echo "usage: sbatch msi_sl3_projective_compact_section.sbatch PRIME PROJECT_HOME" >&2
    exit 2
fi

PROJECTIVE_PRIME="$1"
PROJECTIVE_HOME="$2"
TOOLS_DIR="$PROJECTIVE_HOME/research-tools"
COMPACT_PREFIX="$TOOLS_DIR/projective-cellular-p$PROJECTIVE_PRIME"

module load sagemath/10.7
export DOT_SAGE="$PROJECTIVE_HOME/.sage"
cd "$TOOLS_DIR"

echo "stage=exact-harmonic-discriminant prime=$PROJECTIVE_PRIME"
sage -python sl3_projective_cellular_analyze.py \
    "$COMPACT_PREFIX.tsv" \
    "$COMPACT_PREFIX-summary.json" \
    --harmonic-output "$COMPACT_PREFIX-harmonic.tsv" \
    --lift-output "$COMPACT_PREFIX-qsharp-lifts.tsv"

for BASIS_ROW in 0 1; do
    echo "stage=affine-lattice-reduction prime=$PROJECTIVE_PRIME basis=$BASIS_ROW"
    sage -python sl3_projective_cellular_cvp.py \
        "$COMPACT_PREFIX.tsv" \
        "$COMPACT_PREFIX-qsharp-lifts.tsv" \
        "$COMPACT_PREFIX-summary.json" \
        "$COMPACT_PREFIX-cvp-basis$BASIS_ROW.json" \
        "$COMPACT_PREFIX-cvp-basis$BASIS_ROW.tsv" \
        --basis-row "$BASIS_ROW" \
        --bkz-block-size 10 \
        --bkz-block-size 20 \
        --bkz-block-size 30 \
        --bkz-loops 2
done

echo "stage=rank-two-section prime=$PROJECTIVE_PRIME"
sage -python sl3_projective_cellular_section.py \
    "$COMPACT_PREFIX-cvp-basis0.tsv" \
    "$COMPACT_PREFIX-cvp-basis1.tsv" \
    "$COMPACT_PREFIX-summary.json" \
    "$COMPACT_PREFIX-section.json"

echo "stage=complete prime=$PROJECTIVE_PRIME"
