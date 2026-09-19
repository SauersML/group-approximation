#!/bin/bash
#SBATCH --job-name=cairn-wedderburn-5
#SBATCH --partition=sioux
#SBATCH --nodelist=acn112
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=16G
#SBATCH --time=00:10:00
#SBATCH --output=/projects/standard/hsiehph/sauer354/cairn-wedderburn/job-%j.out
#SBATCH --error=/projects/standard/hsiehph/sauer354/cairn-wedderburn/job-%j.err

set -euo pipefail

module load python3/3.12.4_anaconda2024.06-1_libmamba
cd /projects/standard/hsiehph/sauer354/cairn-wedderburn
python3 support_packet_wedderburn_tag_capacity.py 5 \
  --output support_packet_wedderburn_tag_capacity_5.json \
  > support_packet_wedderburn_tag_capacity_5.stdout.json
