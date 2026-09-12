#!/bin/bash
#SBATCH --job-name=l14-3win-packet
#SBATCH --array=0-15
#SBATCH --time=01:00:00
#SBATCH --mem=4G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-l14-3win-packet-%A_%a.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 research/artifacts/search-l14-three-winner-near-packet.py \
  --shard "$SLURM_ARRAY_TASK_ID" --shards 16 --support 3
