#!/bin/bash
#SBATCH --job-name=p13-hodge-lean
#SBATCH --time=01:00:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=32G
#SBATCH --output=literal-p13-hodge-build-%j.log

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
/projects/standard/hsiehph/sauer354/.elan/bin/lake build \
  GroupApproximation.Sofic.LiteralP13HodgeCertificate
