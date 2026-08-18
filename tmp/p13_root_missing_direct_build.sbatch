#!/usr/bin/env bash
#SBATCH --account=hsiehph
#SBATCH --partition=agsmall
#SBATCH --cpus-per-task=1
#SBATCH --mem=8G
#SBATCH --time=01:00:00
#SBATCH --output=/projects/standard/hsiehph/sauer354/p13_exact_isolated_20260813/root-direct-build-%j.log

set -euo pipefail

export PATH=/projects/standard/hsiehph/sauer354/.elan/bin:$PATH
cd /projects/standard/hsiehph/sauer354/p13_exact_isolated_20260813/project

for module_path in \
  GroupApproximation/Sofic/TransitionGaugeInvariance \
  GroupApproximation/Leavitt/FinitePairedQuotientObstruction \
  GroupApproximation/Leavitt/RobustPairedQuotientFloor \
  GroupApproximation/Leavitt/FiniteTreeCoupling \
  GroupApproximation/Leavitt/OuterRootLeavittRouting \
  GroupApproximation/Leavitt/ZeroRangeObstruction \
  GroupApproximation/Leavitt/FiniteOutcomeCoarsening \
  GroupApproximation/Leavitt/FiniteNoSignalingPairingBox \
  GroupApproximation/Leavitt/FiniteBinaryFiberDecoder \
  GroupApproximation/Leavitt/PauliCarrierBinaryGap
do
  printf 'BEGIN|%s\n' "$module_path"
  mkdir -p ".lake/build/lib/lean/$(dirname "$module_path")"
  lake env lean -DwarningAsError=true "${module_path}.lean" \
    -o ".lake/build/lib/lean/${module_path}.olean" \
    -i ".lake/build/lib/lean/${module_path}.ilean"
  printf 'GREEN|%s\n' "$module_path"
done
