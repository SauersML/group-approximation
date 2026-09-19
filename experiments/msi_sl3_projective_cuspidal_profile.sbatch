#!/bin/bash
#SBATCH --job-name=sl3-cuspidal-profile
#SBATCH --time=04:00:00
#SBATCH --mem=32G
#SBATCH --cpus-per-task=1

set -euo pipefail

if [ "$#" -ne 2 ]; then
    echo "usage: sbatch msi_sl3_projective_cuspidal_profile.sbatch PRIME PROJECT_HOME" >&2
    exit 2
fi

PROJECTIVE_PRIME="$1"
PROJECTIVE_HOME="$2"
TOOLS_DIR="$PROJECTIVE_HOME/research-tools"
GAP_ROOTS="$PROJECTIVE_HOME/gaproot;/opt/sage/local/lib/gap;/opt/sage/local/share/gap"
COMPACT_PREFIX="$TOOLS_DIR/projective-cellular-p$PROJECTIVE_PRIME"
FULL_PREFIX="$TOOLS_DIR/projective-h2-p$PROJECTIVE_PRIME-coupling"

module load sagemath/10.7
export DOT_SAGE="$PROJECTIVE_HOME/.sage"
cd "$TOOLS_DIR"

echo "stage=compact-export prime=$PROJECTIVE_PRIME"
echo "LoadPackage(\"hap\"); PROJECTIVE_CELLULAR_PRIME:=$PROJECTIVE_PRIME; PROJECTIVE_CELLULAR_OUTPUT:=\"$COMPACT_PREFIX.tsv\"; Read(\"sl3_projective_cellular_export.g\"); QUIT;" \
    | sage -gap -q -l "$GAP_ROOTS"

echo "stage=compact-analysis prime=$PROJECTIVE_PRIME"
sage -python sl3_projective_cellular_analyze.py \
    "$COMPACT_PREFIX.tsv" \
    "$COMPACT_PREFIX-summary.json" \
    --harmonic-output "$COMPACT_PREFIX-harmonic.tsv"

if [ ! -s "$COMPACT_PREFIX-harmonic.tsv" ]; then
    echo "prime=$PROJECTIVE_PRIME has no rational degree-two harmonic class"
    exit 0
fi

echo "stage=full-hap-export prime=$PROJECTIVE_PRIME"
echo "LoadPackage(\"hap\"); PROJECTIVE_H2_PRIME:=$PROJECTIVE_PRIME; PROJECTIVE_H2_OUTPUT_PREFIX:=\"$FULL_PREFIX\"; Read(\"sl3_projective_h2_export.g\"); QUIT;" \
    | sage -gap -q -l "$GAP_ROOTS"

echo "stage=two-adic-lift prime=$PROJECTIVE_PRIME"
sage -python sl3_projective_harmonic_primary_hensel.py \
    "$COMPACT_PREFIX.tsv" \
    "$FULL_PREFIX" \
    "$COMPACT_PREFIX-harmonic.tsv" \
    "$TOOLS_DIR/projective-harmonic-primary-p$PROJECTIVE_PRIME-sparse-direct-depth6.json" \
    --depth 6 --direct-time-limit 900

echo "stage=two-local-structure prime=$PROJECTIVE_PRIME"
sage -python sl3_projective_harmonic_primary_structure.py \
    "$COMPACT_PREFIX.tsv" \
    "$FULL_PREFIX" \
    "$COMPACT_PREFIX-harmonic.tsv" \
    "$TOOLS_DIR/projective-harmonic-primary-p$PROJECTIVE_PRIME-sparse-direct-depth6.json" \
    "$TOOLS_DIR/projective-harmonic-primary-p$PROJECTIVE_PRIME-structure.json"

echo "stage=full-plane-section-profile prime=$PROJECTIVE_PRIME"
sage -python sl3_projective_harmonic_primary_section_profile.py \
    "$COMPACT_PREFIX.tsv" \
    "$FULL_PREFIX" \
    "$COMPACT_PREFIX-harmonic.tsv" \
    "$TOOLS_DIR/projective-harmonic-primary-p$PROJECTIVE_PRIME-section-profile.json" \
    --depth 6 --time-limit 900

echo "stage=complete prime=$PROJECTIVE_PRIME"
