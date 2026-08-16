import GroupApproximation.Computability.MarkovMFConsequences

set_option linter.unusedSimpArgs false

-- Undecidability seeds already in Mathlib
#check @Nat.Partrec.Code.halting_problem
#check @ComputablePred
#check @REPred

-- Monoid / congruence machinery for string rewriting
#check @FreeMonoid
#check @Con
#check @conGen
#check @PresentedMonoid
