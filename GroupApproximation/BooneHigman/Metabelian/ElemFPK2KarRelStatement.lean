import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarRelList
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KaroubiStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# `R1` by word length in relative conjugates

Lane `bh-met-92u`, statement module.  Notation: `P = k2DilateSt_pullback s`.  By
`k2KarRel_exists_list` (split relative Steinberg lemma) every `y ∈ ker fst ⊆ St(M, P)` is `l.prod`
for a list `l` of relative conjugates `g x_ij(b) g⁻¹`, `fst b = 0`.

* `k2KarRel_BoundedAt s m`: `R1` restricted to products of at most `m` relative conjugates.
* `k2KarRel_boundedAt_of_injAt`: `R1 → BoundedAt s m` for every `m`.
* `k2KarRel_injAt_of_boundedAt`: `(∀ m, BoundedAt s m) → R1`.
* `k2KarRel_boundedAt_one`: `BoundedAt s 1` is **proved** (a single relative conjugate with
  `snd = 1` is `1`, since `x_ij` is injective and `P ⊆ A × L[X]`).
* `k2KarRel_PosBoundedStatement m`, `k2KarRel_posBounded_of_pos`, `k2KarRel_pos_of_posBounded`.

## LOUD: status

* The family `∀ m, k2KarRel_PosBoundedStatement m` is **LOGICALLY EQUIVALENT** to
  `k2Karoubi_PosStatement` (`R1`): both directions are proved.  It is **not** the isolated
  statement.
* **The isolated statement is `k2KarRel_PairStatement`** (`m = 2`): `R1` for products of two
  relative conjugates.  `k2KarRel_pair_of_pos : k2Karoubi_PosStatement → k2KarRel_PairStatement`
  is proved, so it is **true whenever `R1` is** (and `R1` is believed true: see the truth check
  of `ElemFPK2KaroubiStatement`).  It is a **special case** of `R1` (strictly smaller in proof
  content); its strict weakness is **NOT proved**, and its truth is **OPEN** here.
* The `m = 1` case is proved (`k2KarRel_posBounded_one`).  The `D`-words of
  `ElemFPK2KarRelDWord` (`k2KarRel_D_dies`) are proved to die; they are the discrepancy words
  arising when the witness `W(t, a, n; h)` is re-chosen, which is the ambiguity any pair argument
  must control.
-/

universe u

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

section KarRelStatement

theorem k2KarRel_prod_mem_ker {A : Type*} [CommRing A] {s : A} {M : ℕ}
    {l : List (SteinbergGroup (Fin M) (k2DilateSt_pullback s))}
    (hl : ∀ z ∈ l, z ∈ k2KarRel_gens s M) : l.prod ∈ k2PullRel_ker s M :=
  list_prod_mem fun z hz ↦ k2KarRel_gens_mem_ker (hl z hz)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_prod_mem_ker

/-- **`R1` for products of at most `m` relative conjugates.** -/
def k2KarRel_BoundedAt {A : Type u} [CommRing A] (s : A) (m : ℕ) : Prop :=
  ∀ (M : ℕ) (l : List (SteinbergGroup (Fin M) (k2DilateSt_pullback s))), l.length ≤ m →
    (∀ z ∈ l, z ∈ k2KarRel_gens s M) → ringMap (k2PullRel_snd s) l.prod = 1 →
      cubeDiagDilate_StDies l.prod

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_BoundedAt

theorem k2KarRel_boundedAt_of_injAt {A : Type u} [CommRing A] {s : A}
    (h : k2Karoubi_InjAt s) (m : ℕ) : k2KarRel_BoundedAt s m :=
  fun M l _ hl hsnd ↦ h M l.prod (k2PullRel_mem_ker.mp (k2KarRel_prod_mem_ker hl)) hsnd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_boundedAt_of_injAt

/-- **Reduction** (the whole family is equivalent to `R1`). -/
theorem k2KarRel_injAt_of_boundedAt {A : Type u} [CommRing A] {s : A}
    (h : ∀ m, k2KarRel_BoundedAt s m) : k2Karoubi_InjAt s := by
  intro M y h₁ h₂
  obtain ⟨l, hl, rfl⟩ := k2KarRel_exists_list (k2PullRel_mem_ker.mpr h₁)
  exact h l.length M l le_rfl hl h₂

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_injAt_of_boundedAt

theorem k2KarRel_boundedAt_mono {A : Type u} [CommRing A] {s : A} {m m' : ℕ} (hm : m ≤ m')
    (h : k2KarRel_BoundedAt s m') : k2KarRel_BoundedAt s m :=
  fun M l hlen hl hsnd ↦ h M l (hlen.trans hm) hl hsnd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_boundedAt_mono

/-- **One relative conjugate**: if `snd (g x_ij(b) g⁻¹) = 1` and `fst b = 0` then `b = 0`. -/
theorem k2KarRel_boundedAt_one {A : Type u} [CommRing A] (s : A) : k2KarRel_BoundedAt s 1 := by
  intro M l hlen hl hsnd
  rcases l with _ | ⟨z, _ | ⟨w, l⟩⟩
  · rw [List.prod_nil]
    exact cubeDiagDilate_stDies_one
  · rw [List.prod_cons, List.prod_nil, mul_one] at hsnd ⊢
    obtain ⟨g, i, j, hij, b, hb, rfl⟩ := hl z (List.mem_singleton_self z)
    rw [map_mul, map_mul, map_inv, ringMap_x, conj_eq_one_iff] at hsnd
    have hb2 : k2PullRel_snd s b = 0 :=
      x_injective i j hij (hsnd.trans (x_zero i j hij).symm)
    have hb0 : b = 0 := k2PullRel_ext (by rw [hb, map_zero]) (by rw [hb2, map_zero])
    rw [hb0, x_zero, mul_one, mul_inv_cancel]
    exact cubeDiagDilate_stDies_one
  · rw [List.length_cons, List.length_cons] at hlen
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_boundedAt_one

/-- `BoundedAt` for the proper constants with `k ≥ 1`. -/
def k2KarRel_PosBoundedStatement (m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → ∀ s₀ : MvPolynomial (Fin k) (ZMod p),
    s₀ ≠ 0 → ¬ IsUnit s₀ →
      k2KarRel_BoundedAt (Polynomial.C s₀ : Polynomial (MvPolynomial (Fin k) (ZMod p))) m

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_PosBoundedStatement

theorem k2KarRel_posBounded_of_pos (h : k2Karoubi_PosStatement) (m : ℕ) :
    k2KarRel_PosBoundedStatement m :=
  fun p hp k hk s₀ h0 hu ↦ k2KarRel_boundedAt_of_injAt (h p hp k hk s₀ h0 hu) m

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_posBounded_of_pos

/-- **Reduction**: the bounded family gives `R1` (LOUD: the family is equivalent to `R1`). -/
theorem k2KarRel_pos_of_posBounded (h : ∀ m, k2KarRel_PosBoundedStatement m) :
    k2Karoubi_PosStatement :=
  fun p hp k hk s₀ h0 hu ↦ k2KarRel_injAt_of_boundedAt fun m ↦ h m p hp k hk s₀ h0 hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_pos_of_posBounded

theorem k2KarRel_posBounded_one : k2KarRel_PosBoundedStatement 1 :=
  fun _ _ _ _ _ _ _ ↦ k2KarRel_boundedAt_one _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_posBounded_one

/-- **The isolated statement (LOUD)**: `R1` for products of two relative conjugates.  Implied by
`R1` (`k2KarRel_pair_of_pos`), hence true if `R1` is; a special case of `R1`, strictly smaller
in proof content.  Strict weakness is NOT proved; truth is OPEN here. -/
def k2KarRel_PairStatement : Prop :=
  k2KarRel_PosBoundedStatement 2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_PairStatement

theorem k2KarRel_pair_of_pos (h : k2Karoubi_PosStatement) : k2KarRel_PairStatement :=
  k2KarRel_posBounded_of_pos h 2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_pair_of_pos

end KarRelStatement

end GroupApproximation.BooneHigman.Metabelian.ElemFP
