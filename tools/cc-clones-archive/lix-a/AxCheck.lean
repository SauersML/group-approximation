import GroupApproximation.Computability.WordProblemRE
import GroupApproximation.Computability.BooneWordProblemUndecidable
import GroupApproximation.Computability.AdianRabinVariantTransform

open GroupApproximation

-- D2: the word problem of a finite presentation is r.e.
#print axioms GroupApproximation.WordProblemRE.rePred_wordProblemPred

-- D4': the uniform word problem on presentation codes is undecidable
#print axioms GroupApproximation.Computability.not_computablePred_wordProblemPred

-- D5 + D6: the assembled Adian--Rabin reduction, all four fields
#print axioms GroupApproximation.AdianRabinVariantTransform.reduction
#print axioms GroupApproximation.AdianRabinVariantTransform.correct_raw
#print axioms GroupApproximation.RawTransformPrimrec.computable_rawTransform

-- the endpoint, both halves
#print axioms GroupApproximation.Computability.operatorMF_recognition_not_computable
#print axioms GroupApproximation.WordProblemRE.operatorMF_negative_side_not_re
#print axioms GroupApproximation.WordProblemRE.not_rePred_compl_wordProblemPred

-- the statements, printed so the claim text can be checked against them
#check @GroupApproximation.WordProblemRE.rePred_wordProblemPred
#check @GroupApproximation.Computability.not_computablePred_wordProblemPred
#check @GroupApproximation.Computability.operatorMF_recognition_not_computable
#check @GroupApproximation.WordProblemRE.operatorMF_negative_side_not_re
#check @GroupApproximation.AdianRabinVariantTransform.reduction
