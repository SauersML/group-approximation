#!/usr/bin/env bash
#SBATCH --account=hsiehph
#SBATCH --partition=agsmall
#SBATCH --cpus-per-task=1
#SBATCH --mem=16G
#SBATCH --time=01:00:00
#SBATCH --output=/projects/standard/hsiehph/sauer354/p13_exact_isolated_20260813/endpoint-ci-repairs-%j.log

set -euo pipefail
export PATH=/projects/standard/hsiehph/sauer354/.elan/bin:$PATH
cd /projects/standard/hsiehph/sauer354/p13_exact_isolated_20260813/project

for module_path in \
  GroupApproximation/Sofic/TorsionFreeFiniteNormalLimit \
  GroupApproximation/Sofic/LiteralUniformObstruction \
  GroupApproximation/Sofic/LiteralWitnessConsequences \
  GroupApproximation/Sofic/LiteralSixGenerator \
  GroupApproximation/Sofic/ManuscriptExactWrappers \
  GroupApproximation/Sofic/SoficDirectedUnion \
  GroupApproximation/Sofic/SoficFiniteKernelSemidirect \
  GroupApproximation/Sofic/IntegralLinearResiduallyFinite
do
  printf 'BEGIN|%s\n' "$module_path"
  mkdir -p ".lake/build/lib/lean/$(dirname "$module_path")"
  lake env lean -DwarningAsError=true "${module_path}.lean" \
    -o ".lake/build/lib/lean/${module_path}.olean" \
    -i ".lake/build/lib/lean/${module_path}.ilean"
  printf 'GREEN|%s\n' "$module_path"
done
