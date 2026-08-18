#!/usr/bin/env bash
#SBATCH --account=hsiehph
#SBATCH --partition=agsmall
#SBATCH --cpus-per-task=1
#SBATCH --mem=16G
#SBATCH --time=01:00:00
#SBATCH --output=/projects/standard/hsiehph/sauer354/p13_exact_isolated_20260813/endpoint-audit-%j.log

set -euo pipefail
export PATH=/projects/standard/hsiehph/sauer354/.elan/bin:$PATH
cd /projects/standard/hsiehph/sauer354/p13_exact_isolated_20260813/project
lake env lean -DwarningAsError=true scripts/Audit.lean
