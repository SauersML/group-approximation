import GroupApproximation.Leavitt.PrefixCode
import GroupApproximation.Leavitt.UniversalLeavittOver
import GroupApproximation.Meta.AxiomGuard

/-!
# Frame cone at rank four: definitions and the word-multiplier interface

Khanh (arXiv:2609.08428), Definition `def:ordered-frames`:

> The ordered frame semisimplicial set `X_r(A)` has as its `p`-simplices the tuples
> `(v_1,…,v_k)`, where `k = p+1 ≤ r`, admitting a decomposition
> `A^r = v_1A ⊕ ⋯ ⊕ v_kA ⊕ C`, with `C ≅ A^{r-k}`.

Such a decomposition is the same as an invertible `r × r` matrix whose first `k` columns are
`v_1, …, v_k` (the remaining columns are the image of a basis of `C`). `IsFrame f` below uses
this first-columns matrix form, matching `FrameFan.IsFrameVertex/Edge/Triangle`; lane 07's
`LeavittK2.IsFrame` (`Frame/Complex.lean`, columns along an embedding `Fin k ↪ Fin n`) is a
different packaging, so this list predicate is local to `LeavittK2.FrameCone`.

Khanh, Lemma `lem:word-multiplier`:

> Given finitely many nonzero `a_1,…,a_s ∈ R`, there are `x ∈ R` and nonempty positive words
> `η_1,…,η_s` such that `η_i^* a_i x = 1` for every `i`.

This is lane 08 (`LeavittK2.exists_word_multiplier`); it is recorded here as
`WordMultiplierStatement`, the only external input of `frame_cone_four_of_wordMultiplier`
(`FrameCone/Endpoint.lean`), and discharged by lane 08 in `FrameCone/Main.lean`.

Route (Khanh Prop. `prop:frame-cone`, eq. `cone-coordinate-inverses`), scalarized through the
left-comb self-similarity `M_4(L) ≅ L`, `d_j = s_{1^j0}` (`j < 3`), `d_3 = s_{111}`:
a frame of length `k ≤ 2` is a unit `U` with `U d_j = Σ_i d_i f_j(i)`; `ρ = t_{1^k}`,
`σ = s_{1^k}`, `a = ρ U⁻¹ ≠ 0`; the word multiplier gives `x` and `η`; with `p = U⁻¹ x`,
`y = ρ p`, `b = η^*` one has `b y = 1`, and `U · T · Ẑ · P` is the required completion, where
`P` permutes the leaves, `Ẑ` is the corner unit `y t_0 + s t_1` on `σ A` (`s` a sibling
complement of `η`), and `T` is the shear `1 + (1 - σρ) p b ρ`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone

open GroupApproximation

/-- A list `f` of vectors in `A^n` is an ordered frame when `f.length ≤ n` and its entries are
the first `f.length` columns of an invertible `n × n` matrix (Khanh, Def. `def:ordered-frames`). -/
def IsFrame {A : Type*} [Ring A] {n : ℕ} (f : List (Fin n → A)) : Prop :=
  f.length ≤ n ∧ ∃ g : (Matrix (Fin n) (Fin n) A)ˣ,
    ∀ (j : Fin n) (hj : j.val < f.length) (i : Fin n),
      (g : Matrix (Fin n) (Fin n) A) i j = (f[j.val]'hj) i

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.IsFrame

/-- **Lane 08 interface (Khanh, Lemma `lem:word-multiplier`).** For finitely many nonzero
elements `a_i` of `L = L_{F_2}(1,2)` there are `x` and nonempty words `η_i` with
`η_i^* a_i x = 1`. TRUE by Khanh's normal-form argument. -/
def WordMultiplierStatement : Prop :=
  ∀ (s : ℕ) (a : Fin s → BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)), (∀ i, a i ≠ 0) →
    ∃ x : BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2), ∃ η : Fin s → List (Fin 2),
      (∀ i, η i ≠ []) ∧
        ∀ i, (BinaryLeavitt.family (ZMod 2)).wordT (η i) * a i * x = 1

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.WordMultiplierStatement

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone
