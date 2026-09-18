import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.NKAugmentation
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Ultramatricial
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFieldK2.FieldK2

/-!
# Lane 3b endpoint: the half rings over an ultramatricial `𝔽₂`-ring (lane LVSkewLaurentK2-3b)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  Stable `K₂` of the
half rings `S[t^{±1};φ^{±1}]` splits as `K₂(S) ⊕ NK₂(S,φ)_±` (Ara–Brustenga–Cortiñas 2009,
`thm:skewyao`, Steps 1-2, `yaoseq6.tex` l.574-640; Yao 1995, Thm 2.1).  The summand `K₂(S)`
vanishes for ultramatricial `𝔽₂`-rings by `LVCohnK2.stableK2Trivial_of_isUltramatricialF2`
(Morita invariance, finite products and directed unions) together with
`LVFieldK2.stableK2Trivial_zmodTwo` (Steinberg 1962; Milnor, *Introduction to algebraic
K-theory*, §10).  This file discharges that summand, so that `HalfK2Statement S` depends only on
twisted nil-`K₂` (`NilK2Trivial`, `yaoseq6.tex` l.1169ff).
-/

namespace GroupApproximation.Full.LVSkewLaurentK2

/-- **Lane 3b, reduced to twisted nil-`K₂`.**  For an ultramatricial `𝔽₂`-ring `S`, the half
rings `S[t;φ]` and `S[t⁻¹;φ⁻¹]` have stable `K₂ = 0` as soon as `NK₂(S,φ)_± = 0`.
(`yaoseq6.tex` `thm:skewyao`, Steps 1-2, l.574-640, and l.1169ff; Yao 1995, Thm 2.1;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem halfK2Statement_of_ultramatricial_of_nilK2Trivial {S : Type*} [Ring S]
    [MulSemiringAction (Multiplicative ℤ) S] (hS : IsUltramatricialF2 S)
    (hpos : NilK2Trivial S 1 one_ne_zero) (hneg : NilK2Trivial S (-1) (by decide)) :
    HalfK2Statement S :=
  halfK2Statement_of_nilK2Trivial S
    (LVCohnK2.stableK2Trivial_of_isUltramatricialF2 LVFieldK2.stableK2Trivial_zmodTwo hS)
    hpos hneg

end GroupApproximation.Full.LVSkewLaurentK2
