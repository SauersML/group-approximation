#!/bin/bash
#SBATCH --job-name=sl3-prime-power
#SBATCH --time=08:00:00
#SBATCH --mem=64G
#SBATCH --cpus-per-task=1

set -euo pipefail

if [ "$#" -ne 2 ]; then
    echo "usage: sbatch msi_sl3_projective_prime_power_screen.sbatch LEVEL PROJECT_HOME" >&2
    exit 2
fi

PROJECTIVE_LEVEL="$1"
PROJECTIVE_HOME="$2"
TOOLS_DIR="$PROJECTIVE_HOME/research-tools"
PREFIX="$TOOLS_DIR/projective-cellular-n$PROJECTIVE_LEVEL"
GAP_ROOT="$PROJECTIVE_HOME/gaproot"

module load sagemath/10.7
export DOT_SAGE="$PROJECTIVE_HOME/.sage"
cd "$TOOLS_DIR"

echo "stage=prime-power-export level=$PROJECTIVE_LEVEL"
echo "LoadPackage(\"hap\"); PROJECTIVE_CELLULAR_LEVEL:=$PROJECTIVE_LEVEL; PROJECTIVE_CELLULAR_OUTPUT:=\"$PREFIX.tsv\"; Read(\"sl3_projective_cellular_prime_power_export.g\"); QUIT;" \
    | sage -gap -q -l "$GAP_ROOT;/opt/sage/local/lib/gap;/opt/sage/local/share/gap"

echo "stage=compact-analysis level=$PROJECTIVE_LEVEL"
sage -python sl3_projective_cellular_analyze.py \
    "$PREFIX.tsv" \
    "$PREFIX-summary.json" \
    --harmonic-output "$PREFIX-harmonic.tsv" \
    --lift-output "$PREFIX-qsharp-lifts.tsv"

echo "stage=complete level=$PROJECTIVE_LEVEL"
