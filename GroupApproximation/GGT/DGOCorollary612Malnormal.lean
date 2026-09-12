import GroupApproximation.GGT.WPDDGOReduction

/-!
# Almost malnormality at a letter of `X`, and Corollary 6.12 from Theorem 6.11

`GGT.dgoCorollary612_of` derives Dahmani--Guirardel--Osin's Corollary 6.12 from
their Theorem 6.11 and their Proposition 4.33.  The second of those is not
needed: the only instance of it the derivation consumes is at the `a` produced
by `exists_mem_base_notMem_fam`, which lies in `D.base`, and at such an `a`
almost malnormality is a consequence of local finiteness alone.

## The three-letter word

Let `a ∈ X \ H` and let `h ∈ H` satisfy `a⁻¹ h a ∈ H`.  Write
`k = a⁻¹ h a`.  Then

    w = [base a, comp () k, base a⁻¹]

spells `a k a⁻¹ = h`, has length three, and every letter is admissible: `a` and
`a⁻¹` lie in `X`, and `k` lies in `H`.  Read from the vertex `1`, its only
`H`-letter is read at the vertex `a`, and `a ∉ H`, so `w` traverses no edge of
`Γ_H` --- `AvoidsFrom` forbids an `H`-letter only at a vertex *of* `H`, which is
exactly Dahmani--Guirardel--Osin's `d̂`, whose forbidden edges are the edges of
`Γ_H` and so have both endpoints in `H`.  Hence

    {h | h ∈ H and a⁻¹ h a ∈ H} ⊆ relBall () 3 ,

and `IsHyperbolicallyEmbedded.locallyFinite` makes that set finite.

`a⁻¹ ∈ X` is not an extra hypothesis: `X ∪ H` is symmetric, so `a⁻¹` lies in it,
and `a⁻¹ ∈ H` would give `a ∈ H`.

## What this does and does not settle

`DGOProposition433` as stated quantifies over every `a ∉ H`, and for a general
`a` the argument above fails: a shortest word for `a` may read an `H`-letter at
a vertex of `H`, and ruling that out is Dahmani--Guirardel--Osin's quadrilateral
argument.  Nothing here proves that statement.  What is proved is that the
chain does not need it: `dgoCorollary612_of_611` obtains `DGOCorollary612` from
`DGOTheorem611` alone.

That reduction has since been overtaken.  `DGOTheorem611` is false as stated ---
it omits `a ∉ H_λ`, and `GGT.DGOTheorem611Refutation.not_dgoTheorem611` refutes
it --- while the statement with that hypothesis added is proved, as
`GGT.dgoTheorem611'`, and so is `GGT.dgoCorollary612 : DGOCorollary612`, in
`GGT/DGOCorollary612Unconditional.lean`, without any of the polygon theory of
§4.2.  So the standing debt of `OsinTheorem12` is **two** named statements,
`DGOTheorem68` and `OsinTheorem54`, and `GGT.osinTheorem12_of_two` assembles it
from them.  `dgoCorollary612_of_611` is kept because it records what the
corollary costs over the citation, not because anything consumes it.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

section Malnormal

variable {G : Type u} [Group G]

/-- **The inverse of a letter of `X` outside `H` is again a letter of `X`.**
The alphabet is symmetric, so `a⁻¹` lies in `X ∪ H`; and it does not lie in `H`,
since `H` is closed under inversion and `a ∉ H`. -/
theorem inv_mem_base_of_notMem_fam (D : RelGenSet G Unit) {a : G}
    (haB : a ∈ D.base) (haH : a ∉ D.fam ()) : a⁻¹ ∈ D.base := by
  rcases D.symmetricGenerating.inv_mem a (Set.mem_union_left _ haB) with h | h
  · exact h
  · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp h
    cases lam
    exact absurd (inv_mem_iff.mp hlam) haH

/-- **Almost malnormality at a letter of `X`.**  For `a ∈ X` outside `H`, the
elements of `H` that `a` conjugates back into `H` all lie in the relative ball
of radius three, which local finiteness makes finite.

This is the instance of Dahmani--Guirardel--Osin's Proposition 4.33 that their
proof of Corollary 6.12 uses, and at a letter of `X` it needs no polygon
theory. -/
theorem finite_conj_inter_of_mem_base (D : RelGenSet G Unit)
    (hemb : D.IsHyperbolicallyEmbedded) {a : G} (haB : a ∈ D.base)
    (haH : a ∉ D.fam ()) :
    {h : G | h ∈ D.fam () ∧ a⁻¹ * h * a ∈ D.fam ()}.Finite := by
  have hainv : a⁻¹ ∈ D.base := inv_mem_base_of_notMem_fam D haB haH
  refine Set.Finite.subset (hemb.locallyFinite () 3) ?_
  rintro h ⟨hh, hk⟩
  refine RelGenSet.mem_relBall.mpr ⟨hh, [RelLetter.base a,
    RelLetter.comp () (a⁻¹ * h * a), RelLetter.base a⁻¹], ?_, ?_, ?_, ?_⟩
  · refine List.forall_mem_cons.mpr ⟨haB, List.forall_mem_cons.mpr ⟨hk, ?_⟩⟩
    exact List.forall_mem_singleton.mpr hainv
  · simp only [RelLetter.listVal, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, RelLetter.val]
    group
  · refine ⟨?_, ?_, ?_, trivial⟩
    · rintro ⟨hc, -⟩
      exact hc
    · rintro ⟨-, hv⟩
      rw [one_mul] at hv
      exact haH hv
    · rintro ⟨hc, -⟩
      exact hc
  · simp

end Malnormal

/-! ## Corollary 6.12 from Theorem 6.11 alone -/

/-- **Dahmani--Guirardel--Osin's Corollary 6.12 costs only their Theorem 6.11.**
Their proof is reproduced as `dgoCorollary612_of` reproduces it --- unboundedness
from local finiteness and infinitude, then Theorem 6.11 --- with the finite
intersection supplied by `finite_conj_inter_of_mem_base` rather than cited from
Proposition 4.33.  The `a` is the one `exists_mem_base_notMem_fam` produces, and
it lies in `D.base`, which is what that lemma asks for. -/
theorem dgoCorollary612_of_611 (h611 : DGOTheorem611.{u}) : DGOCorollary612.{u} := by
  intro G _ D hemb hnd
  obtain ⟨a, haB, haH⟩ := exists_mem_base_notMem_fam D hnd.1
  obtain ⟨h, -, hlox⟩ :=
    h611 G D hemb (not_subset_relBall_of_infinite D hemb hnd.2) a haB
      (finite_conj_inter_of_mem_base D hemb haB haH)
  exact ⟨a * h, hlox⟩

/-- **`OsinTheorem12` costs three citations, not four.**  `dgoCorollary612_of`
left `DGOProposition433` beside `DGOTheorem611`; it is now discharged. -/
theorem osinTheorem12_of_611 (h68 : DGOTheorem68.{u, v}) (h54 : OsinTheorem54.{u})
    (h611 : DGOTheorem611.{u}) : OsinTheorem12.{u, v} :=
  osinTheorem12_of_612 h68 h54 (dgoCorollary612_of_611 h611)

end GGT
end GroupApproximation
