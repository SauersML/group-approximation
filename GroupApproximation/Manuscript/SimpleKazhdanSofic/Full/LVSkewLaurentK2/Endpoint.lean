import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.YaoReduction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.Units
-- import <3b file providing halfK2Statement_of_ultramatricial>
-- import <YaoCore file providing yaoFactorization_of_ultramatricial>

/-!
# Stable `K₂ = 0` of skew Laurent rings over ultramatricial `𝔽₂`-rings (WO-LVCohnK2-3)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.
Ara–Brustenga–Cortiñas 2009, `thm:skewyao` in degree two (`yaoseq6.tex` l.574-640).
-/

namespace GroupApproximation.Full.LVSkewLaurentK2

/-- **WO-LVCohnK2-3.**  Stable `K₂(S[t,t⁻¹;φ]) = 0` for an ultramatricial `𝔽₂`-ring `S` with an
automorphism.  (ABC 2009 `thm:skewyao`; `simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem stableK2Trivial_skewLaurent_of_ultramatricial {S : Type*} [Ring S]
    [MulSemiringAction (Multiplicative ℤ) S]
    (hS : ∀ s : Finset S, ∃ (k : ℕ) (d : Fin (k + 1) → ℕ) (T : Subring S), (s : Set S) ⊆ T ∧
      Nonempty (T ≃+* ((j : Fin (k + 1)) → Matrix (Fin (d j)) (Fin (d j)) (ZMod 2)))) :
    LVH2GL3.StableK2Trivial (SkewMonoidAlgebra S (Multiplicative ℤ)) :=
  stableK2Trivial_of_yaoFactorization (k1Statement_of_ultramatricial hS)
    (halfK2Statement_of_ultramatricial hS) (yaoFactorization_of_ultramatricial hS)

end GroupApproximation.Full.LVSkewLaurentK2
