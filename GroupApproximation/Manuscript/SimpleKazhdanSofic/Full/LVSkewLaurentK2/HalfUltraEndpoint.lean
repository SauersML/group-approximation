import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.HalfUltraEquiv
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.NKAugmentation
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Ultramatricial
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFieldK2.FieldK2

/-!
# `HalfK2Statement` for ultramatricial rings, up to positive nil-`K₂` (lane sk-lv-03)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii; `frontier/SK.md`,
section 2b, items 10-11.

**The target `halfK2Statement_of_ultramatricial` is NOT proved here.**  The suggested route
(a directed union of half rings over finite stages, then
`stableK2Trivial_skewHalf_of_subrings`) needs every finite subset of `S` to lie in a
finite-dimensional subring `T` with `φ(T) = T`.  The exact Lean statement quantifies over an
*arbitrary* action of `Multiplicative ℤ` on `S`, and `IsUltramatricialF2 S` says nothing about
it.  Even for the manuscript's ring, no finite-dimensional subalgebra is `φ̂`-stable (see
`NKVanishing.lean`).  Without stable stages the half ring is not a union of half rings of
matrix algebras over `𝔽₂`, and the only remaining route is twisted `NK₂`-vanishing for regular
supercoherent rings (Ara–Brustenga–Cortiñas 2009, `yaoseq6.tex` l.1169ff; Quillen's
`K₂(𝔽₂[t]) = 0` at a matrix stage).  Neither is in the corpus.

**Truth.**  `HalfK2Statement S` holds for every ultramatricial `𝔽₂`-ring `S` and every
automorphism `φ`: such `S` is von Neumann regular, hence regular supercoherent, so
`NK₂(S,φ)_± = 0` and `K₂(S) = 0`.  The exact statement is therefore true but open in the
corpus.

**Remaining gap: `skHalfK2_posNilStatement`**, the vanishing of the *positive* twisted nil-`K₂`
`NilK2Trivial S 1` for every ultramatricial `𝔽₂`-ring with every action.

* It is **true**, as above.
* **LOUD: it is not strictly weaker in logical strength.**  Quantified over all `S`, it is
  equivalent to the quantified target.  `halfK2Statement_iff_nilK2Trivial` gives one
  direction, and the other is `skHalfK2_halfK2Statement_of_posNil`.
* It is **strictly smaller in proof content**.  Before this file the target needed three
  inputs: `K₂(S) = 0`, `NilK2Trivial S 1` and `NilK2Trivial S (-1)`
  (`halfK2Statement_of_ultramatricial_of_nilK2Trivial`).  Here `K₂(S) = 0` comes from
  `LVCohnK2.stableK2Trivial_of_isUltramatricialF2`.  The negative half comes from the positive
  half of the reversed action, by `skHalfK2_negHalfEquiv`, which is proved.

`skHalfK2_halfK2Statement_of_nilK2Trivial_rev` is the per-ring form.
-/

universe u

namespace GroupApproximation.Full.LVSkewLaurentK2

/-- **Remaining gap of lane sk-lv-03**: positive twisted nil-`K₂` vanishes for every
ultramatricial `𝔽₂`-ring and every action (`NK₂(S,φ)_+ = 0`; `yaoseq6.tex` l.1169ff).  This is
true, because ultramatricial rings are regular supercoherent.  It is equivalent to the
quantified target, but it is strictly smaller in proof content: see the module docstring.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skHalfK2_posNilStatement : Prop :=
  ∀ (S : Type u) [Ring S] [MulSemiringAction (Multiplicative ℤ) S],
    IsUltramatricialF2 S → NilK2Trivial S 1 one_ne_zero

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_posNilStatement

/-- **Per-ring form.**  For an ultramatricial `𝔽₂`-ring `S`, `HalfK2Statement S` follows from
positive twisted nil-`K₂` vanishing for `φ` and for `φ⁻¹`.  `K₂(S) = 0` is proved, and the
negative half ring is the positive half ring of `φ⁻¹` (`skHalfK2_negHalfEquiv`).
(`yaoseq6.tex` `thm:skewyao`, Steps 1-2; `simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem skHalfK2_halfK2Statement_of_nilK2Trivial_rev {S : Type*} [Ring S]
    [MulSemiringAction (Multiplicative ℤ) S] (hS : IsUltramatricialF2 S)
    (hpos : NilK2Trivial S 1 one_ne_zero)
    (hrev : NilK2Trivial (skHalfK2_Rev S) 1 one_ne_zero) :
    HalfK2Statement S := by
  have hK2 : LVH2GL3.StableK2Trivial S :=
    LVCohnK2.stableK2Trivial_of_isUltramatricialF2 LVFieldK2.stableK2Trivial_zmodTwo hS
  have hS' : IsUltramatricialF2 (skHalfK2_Rev S) := skHalfK2_isUltramatricialF2_rev S hS
  have hK2' : LVH2GL3.StableK2Trivial (skHalfK2_Rev S) :=
    LVCohnK2.stableK2Trivial_of_isUltramatricialF2 LVFieldK2.stableK2Trivial_zmodTwo hS'
  have h1 : LVH2GL3.StableK2Trivial (skewHalf S 1) :=
    LVStableK2.stableK2Trivial_of_baseSurjective (halfConst S 1)
      (baseSurjective_halfConst_of_nilK2Trivial S 1 one_ne_zero hpos) hK2
  have h1' : LVH2GL3.StableK2Trivial (skewHalf (skHalfK2_Rev S) 1) :=
    LVStableK2.stableK2Trivial_of_baseSurjective (halfConst (skHalfK2_Rev S) 1)
      (baseSurjective_halfConst_of_nilK2Trivial (skHalfK2_Rev S) 1 one_ne_zero hrev) hK2'
  show LVH2GL3.StableK2Trivial (skewHalf S 1) ∧ LVH2GL3.StableK2Trivial (skewHalf S (-1))
  exact ⟨h1, LVCohnK2.stableK2Trivial_of_ringEquiv (skHalfK2_negHalfEquiv S).symm h1'⟩

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_halfK2Statement_of_nilK2Trivial_rev

/-- **Endpoint of lane sk-lv-03**: `skHalfK2_posNilStatement` gives the target
`HalfK2Statement S` for every ultramatricial `𝔽₂`-ring `S` (the conclusion of
`halfK2Statement_of_ultramatricial`, `Interface.lean` l.36).
(`yaoseq6.tex` `thm:skewyao`, Steps 1-2; `simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem skHalfK2_halfK2Statement_of_posNil (hQ : skHalfK2_posNilStatement.{u}) {S : Type u}
    [Ring S] [MulSemiringAction (Multiplicative ℤ) S] (hS : IsUltramatricialF2 S) :
    HalfK2Statement S :=
  skHalfK2_halfK2Statement_of_nilK2Trivial_rev hS (hQ S hS)
    (hQ (skHalfK2_Rev S) (skHalfK2_isUltramatricialF2_rev S hS))

#audit_axioms GroupApproximation.Full.LVSkewLaurentK2.skHalfK2_halfK2Statement_of_posNil

end GroupApproximation.Full.LVSkewLaurentK2
