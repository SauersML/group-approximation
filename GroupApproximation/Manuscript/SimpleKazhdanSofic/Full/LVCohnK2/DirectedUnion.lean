import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Coefficients

/-!
# Stable `K₂ = 0` passes to directed unions (lane LVCohnK2)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  In the
Ara–Brustenga–Cortiñas computation of `K_*(C_2(𝔽₂))` (Münster J. Math. 2 (2009), proof of
Thm 3.6 and Sec. 5) the degree-zero part `C_0` of the Cohn algebra is the directed union of the
finite-dimensional semisimple algebras `B_k ≅ 𝔽₂ × M_2(𝔽₂) × ⋯ × M_{2^k}(𝔽₂)`, and `K`-theory
commutes with directed unions.  This file proves the degree-two, finite-stage form of that
continuity for an arbitrary ring `S`:

* `liftableSubgroup I S`: the elements of `St_I(S)` that lift to `St_I(T)` for every subring `T`
  containing a fixed finite set of coefficients; it is a subgroup;
* `exists_finset_lift`: every element of `St_I(S)` is liftable (the subgroup contains the
  generators `x_{ij}(a)`, with the finite set `{a}`);
* `stableK2Trivial_of_subrings`: if every finite subset of `S` lies in a subring with stable
  `K₂ = 0`, then `S` has stable `K₂ = 0`.
-/

namespace GroupApproximation.Full.LVCohnK2

open SteinbergGroup

section Lift

variable (I : Type*) [Fintype I] [DecidableEq I] (S : Type*) [Ring S]

/-- Elements of `St_I(S)` that lift to `St_I(T)` along `T ↪ S` for every subring `T` containing
some fixed finite set of coefficients.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
def liftableSubgroup : Subgroup (SteinbergGroup I S) where
  carrier := {k | ∃ s : Finset S, ∀ T : Subring S, (s : Set S) ⊆ (T : Set S) →
    k ∈ (ringMap (I := I) T.subtype).range}
  one_mem' := ⟨∅, fun T _ => one_mem (ringMap (I := I) T.subtype).range⟩
  mul_mem' := by
    classical
    rintro a b ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s ∪ t, fun T hT => mul_mem (hs T ?_) (ht T ?_)⟩
    · exact fun c hc => hT (Finset.mem_coe.mpr (Finset.mem_union_left t (Finset.mem_coe.mp hc)))
    · exact fun c hc => hT (Finset.mem_coe.mpr (Finset.mem_union_right s (Finset.mem_coe.mp hc)))
  inv_mem' := by
    rintro a ⟨s, hs⟩
    exact ⟨s, fun T hT => inv_mem (hs T hT)⟩

/-- Every element of `St_I(S)` involves only finitely many coefficients: it lifts to `St_I(T)`
for every subring `T` containing a suitable finite set.  (`simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
theorem exists_finset_lift (k : SteinbergGroup I S) :
    ∃ s : Finset S, ∀ T : Subring S, (s : Set S) ⊆ (T : Set S) →
      k ∈ (ringMap (I := I) T.subtype).range := by
  have hk : k ∈ liftableSubgroup I S := by
    refine PresentedGroup.generated_by (relations (I := I) (R := S)) (liftableSubgroup I S)
      ?_ k
    rintro ⟨i, j, hij, a⟩
    refine ⟨{a}, fun T hT => ?_⟩
    have ha : a ∈ T :=
      SetLike.mem_coe.mp (hT (Finset.mem_coe.mpr (Finset.mem_singleton_self a)))
    refine MonoidHom.mem_range.mpr ⟨x i j hij ⟨a, ha⟩, ?_⟩
    exact ringMap_x T.subtype i j hij ⟨a, ha⟩
  exact hk

end Lift

/-- **Directed unions.**  If every finite set of coefficients of `S` lies in a subring with
stable `K₂ = 0`, then `S` has stable `K₂ = 0`: lift `k ∈ K₂(n, S)` to such a subring `T`, where
it lies in `K₂(n, T)` by injectivity of `E_n(T) → E_n(S)`, kill it after padding, and push the
relation back to `S`.  (Ara–Brustenga–Cortiñas 2009, continuity of `K`-theory in the proof of
Thm 3.6; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem stableK2Trivial_of_subrings {S : Type*} [Ring S]
    (hS : ∀ s : Finset S, ∃ T : Subring S, (s : Set S) ⊆ (T : Set S) ∧
      LVH2GL3.StableK2Trivial T) :
    LVH2GL3.StableK2Trivial S := by
  intro n k hk
  obtain ⟨s, hs⟩ := exists_finset_lift (Fin n) S k
  obtain ⟨T, hsT, hT⟩ := hS s
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp (hs T hsT)
  have hy : projection y = 1 :=
    projection_eq_one_of_ringMap T.subtype T.subtype_injective hk
  obtain ⟨N, hN, hyN⟩ := hT n y hy
  refine ⟨N, hN, ?_⟩
  rw [LVStableK2.indexMap_ringMap, hyN, map_one]

end GroupApproximation.Full.LVCohnK2
