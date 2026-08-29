import GroupApproximation.GGT.HullSCRelatorSeparation2Ball

/-!
# From a span to a block letter's value

The packaged theorem states its relation between the SPANS of two components:
`x · ((vertex 1 q i)⁻¹ * vertex 1 q k) · x' = (vertex 1 s j)⁻¹ * vertex 1 s l`.
The closers want it between the two block letters' VALUES,
`x · a_b^e · x' = a_b^f`.  Over the alternating relator those are the same
thing, because each block letter is its own component
(`HullSC.isComp_relatorWord₂`), so every component of the run spans exactly one
letter and `k = i + 1`.

This module is that step, and it is independent of everything still in flight:
the restatement of the packaged theorem changes which configuration hypotheses
it takes, not what its conclusion says about spans.

* `vertex_succ_of_getElem?` -- one step of the path multiplies by the letter's
  value.
* `span_eq_val_of_getElem?` -- so a span of length one is that value.
* `span_eq_pow_of_block` -- and over a rotation of the relator, reading a block
  letter at an offset, the span is the power the letter carries, in the shape
  `HullSC.listVal_conj_of_alignedMatch_ball` consumes.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section Span

variable {G : Type u} [Group G] {Λ : Type w}

/-- **One step of the path multiplies by the letter's value.** -/
theorem vertex_succ_of_getElem? :
    ∀ (l : List (GGT.RelLetter G Λ)) (i : ℕ) (v : G) (c : GGT.RelLetter G Λ),
      l[i]? = some c →
        GGT.OsinComponents.vertex v l (i + 1)
          = GGT.OsinComponents.vertex v l i * c.val := by
  intro l
  induction l with
  | nil =>
      intro i v c hc
      simp at hc
  | cons d t ih =>
      intro i v c hc
      cases i with
      | zero =>
          rw [List.getElem?_cons_zero] at hc
          have hdc : d = c := Option.some.inj hc
          subst hdc
          rw [GGT.OsinComponents.vertex_cons_succ,
            GGT.OsinComponents.vertex_zero, GGT.OsinComponents.vertex_zero]
      | succ k =>
          rw [List.getElem?_cons_succ] at hc
          rw [GGT.OsinComponents.vertex_cons_succ,
            GGT.OsinComponents.vertex_cons_succ, ih k (v * d.val) c hc]

/-- **A span of length one is the letter's value.** -/
theorem span_eq_val_of_getElem? {l : List (GGT.RelLetter G Λ)} {i : ℕ} {v : G}
    {c : GGT.RelLetter G Λ} (hc : l[i]? = some c) :
    (GGT.OsinComponents.vertex v l i)⁻¹ *
        GGT.OsinComponents.vertex v l (i + 1) = c.val := by
  rw [vertex_succ_of_getElem? l i v c hc, inv_mul_cancel_left]

end Span

section Block

variable {G : Type u} [Group G]

/-- **The span of a block letter of the relator is the power it carries.**

`k = i + 1` is not a choice: over `Λ = Bool` each block letter is its own
maximal component, so a component of the run spans one letter. -/
theorem span_eq_pow_of_block {p : List G} {a : Bool → G} {ms : List ℕ}
    {c : ℕ} {i : ℕ} {b : Bool} {e : ℕ}
    (hlet : ((relatorWord₂ p (a false) (a true) ms).rotate c)[i]?
      = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ e))) :
    (GGT.OsinComponents.vertex (1 : G)
          ((relatorWord₂ p (a false) (a true) ms).rotate c) i)⁻¹ *
        GGT.OsinComponents.vertex (1 : G)
          ((relatorWord₂ p (a false) (a true) ms).rotate c) (i + 1)
      = a b ^ e := by
  rw [span_eq_val_of_getElem? hlet]
  show (if b then a true else a false) ^ e = a b ^ e
  rw [ite_apply_eq a b]

/-- **The mirrored form**: over a rotation of the formal inverse the span is the
inverse of the power. -/
theorem span_eq_pow_inv_of_block {p : List G} {a : Bool → G} {ms : List ℕ}
    {c : ℕ} {i : ℕ} {b : Bool} {e : ℕ}
    (hlet : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c)[i]?
      = some (GGT.RelLetter.comp b (((if b then a true else a false) ^ e)⁻¹))) :
    (GGT.OsinComponents.vertex (1 : G)
          ((RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c) i)⁻¹ *
        GGT.OsinComponents.vertex (1 : G)
          ((RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c)
            (i + 1)
      = (a b ^ e)⁻¹ := by
  rw [span_eq_val_of_getElem? hlet]
  show ((if b then a true else a false) ^ e)⁻¹ = (a b ^ e)⁻¹
  rw [ite_apply_eq a b]

end Block

end HullSC
end GroupApproximation
