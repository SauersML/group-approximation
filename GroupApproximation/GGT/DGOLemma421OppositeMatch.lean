import GroupApproximation.GGT.DGOLemma421OppositeStart

/-!
# Opposite-side matches in start coordinates

The finite-absorption theorem for the DGO quadrilateral returns a component
start on the reversed opposite side together with a coset factor at its
forward endpoint.  This file transports that start to a component of the
forward opposite word and invokes the span adjustment from
`DGOLemma421OppositeStart`, giving the corrected start-coset identity used by
Lemma 4.21(b).
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- An opposite-side endpoint match in a four-gon yields a component of the
forward opposite word and a start-coset identity for the source component. -/
theorem exists_opposite_start_coset_match_421
    (D : RelGenSet G Λ) {lam : Λ}
    {p q r s : List (RelLetter G Λ)}
    {source : Fin (p.length + r.length + 1) → ℕ}
    {i : Fin (p.length + r.length + 1)} {j : ℕ}
    (hj : j ≤ s.length) (hjpos : 0 < j)
    (hstart : IsCompStart lam (p ++ q ++ r ++ revWord s)
      (p.length + q.length + r.length + (s.length - j)))
    (h : G) (hh : h ∈ D.fam lam)
    (heq : RelLetter.listVal p * vertex (1 : G) q (source i) * h =
      vertex (1 : G) s j)
    (hlet : ∀ a ∈ s, D.IsLetter a) :
    ∃ iS : ℕ, IsComp lam s iS j ∧
      ∃ hS : G, hS ∈ D.fam lam ∧
        RelLetter.listVal p * vertex (1 : G) q (source i) * hS =
          vertex (1 : G) s iS := by
  obtain ⟨iS, hcomp⟩ := exists_component_of_opposite_start_421 hj hjpos hstart
  let A : G := RelLetter.listVal p * vertex (1 : G) q (source i)
  obtain ⟨hS, hhS, heqS⟩ := exists_start_coset_of_opposite_end_match D hlet
    hcomp h hh (by simpa [A] using heq)
  refine ⟨iS, hcomp, hS, hhS, ?_⟩
  simpa [A] using heqS

end OsinComponents
end GGT
end GroupApproximation
