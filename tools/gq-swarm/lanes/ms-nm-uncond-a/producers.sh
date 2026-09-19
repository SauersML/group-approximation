#!/usr/bin/env bash
cd /Users/user/nonsofic_existence
for T in CoreModelsLEFStatement CoreRingReflectionStatement ClopenCrossedProductNonzeroDefectStatement TransientIdealLocallyMatricialFTwoStatement ChainCoreDefectCoverStatement CoreKernelElementaryStatement SubshiftCycleConditionLEFInput CoreMFRadicalKillStatement CountableCrossedProductStatement BilateralThreeTransferStatement BilateralThreeCellStatement TransientCellsStatement TorsionDefectTransferStatement; do
  hits=$(git grep -h -E "^(protected )?(theorem|lemma|def|noncomputable def) +[A-Za-z0-9_.']+ *: *([A-Za-z0-9_]*\.)*${T}( |$|\.\{)" origin/main -- 'GroupApproximation/*.lean' | sed -E 's/^(protected )?(theorem|lemma|def|noncomputable def) +([^ :]+).*/\3/' | tr '\n' ' ')
  echo "$T: ${hits:-NONE}"
done
