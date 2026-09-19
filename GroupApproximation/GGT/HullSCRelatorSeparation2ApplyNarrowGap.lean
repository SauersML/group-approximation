import GroupApproximation.GGT.OsinTheorem54SepHypForms

/-!
# The gap side, at the chain's own constant

`GGT.OsinComponents.two_block_conj_of_hyperbolic` proves the two-block
conjugation from four-point hyperbolicity of the RELATIVE Cayley graph
`Γ(G, X ⊔ ℋ)` at every REAL `b ≥ 0` --- the passage to `⌈b⌉₊` is inside it.
This chain spends it at one place only, `b := (bn : ℝ)` with `bn` a natural, so
all that is left here is that instance under the name the rest of the chain
uses.

Three copies of this statement used to stand between the two.  The first
narrowed `two_block_conj_named`'s hypothesis from the isolated-component bound
at every pair to the innermost cut at one pair; the second opened that proof
with `connector_mem_relBall_at` and the tower; both are gone, and what proved
them is now upstream where it belongs.  The reason they were written --- that
the tower supplies the bound at natural `b` only, so the `∀`-form over the
reals was unavailable --- was answered by putting the `⌈b⌉₊` bridge inside the
primary rather than around it.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The two-block conjugation at a natural constant.**
`GGT.OsinComponents.two_block_conj_of_hyperbolic` at `b := (bn : ℝ)`, which is
the only pair this chain spends it at. -/
theorem two_block_conj_named_hyp (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (bn : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ C : ℕ, 0 < C ∧
      ∀ (lam : Λ) (p q r s : List (RelLetter G Λ)) (i k j l : ℕ),
        RelLetter.listVal s = RelLetter.listVal p * RelLetter.listVal q
            * RelLetter.listVal r →
        (∀ a ∈ p ++ q ++ r ++ revWord s, D.IsLetter a) →
        (∀ a ∈ p, ∃ x : G, a = RelLetter.base x) →
        (∀ a ∈ r, ∃ x : G, a = RelLetter.base x) →
        0 < p.length →
        (∀ t : ℕ, t < 4 → ∀ x y : ℕ, fourGonCut p q r s t ≤ x → x ≤ y →
          y ≤ fourGonCut p q r s (t + 1) →
          ((y - x : ℕ) : ℝ) / 1 - (bn : ℝ)
            ≤ ((wordDist D.alphabet.carrier
                (vertex (1 : G) (p ++ q ++ r ++ revWord s) x)
                (vertex (1 : G) (p ++ q ++ r ++ revWord s) y) : ℕ) : ℝ)) →
        IsComp lam q i k → (k < q.length ∨ 0 < r.length) →
        IsComp lam s j l → (l < s.length ∨ 0 < r.length) →
        Connected D.fam lam 1 (p ++ q ++ r ++ revWord s) (p.length + i)
            (p.length + q.length + r.length + (s.length - l)) →
        (∀ t : ℕ, p.length + i < t →
          t < p.length + q.length + r.length + (s.length - l) →
          IsCompStart lam (p ++ q ++ r ++ revWord s) t →
          ¬ Connected D.fam lam 1 (p ++ q ++ r ++ revWord s)
            (p.length + i) t) →
        (∀ o : ℕ,
          (p.length + q.length + r.length + (s.length - l) < o
              ∧ o < (p ++ q ++ r ++ revWord s).length)
            ∨ o < p.length + i →
          IsCompStart lam (p ++ q ++ r ++ revWord s) o →
          ¬ Connected D.fam lam 1 (p ++ q ++ r ++ revWord s)
            (p.length + q.length + r.length + (s.length - l)) o) →
        ((vertex (1 : G) s j)⁻¹ * (RelLetter.listVal p * vertex (1 : G) q i)
            ∈ D.relBall lam (C * 4)) ∧
          ((RelLetter.listVal p * vertex (1 : G) q k)⁻¹ * vertex (1 : G) s l
            ∈ D.relBall lam (C * 4)) :=
  two_block_conj_of_hyperbolic D hsymm hδ (bn : ℝ) (Nat.cast_nonneg bn)

end OsinComponents
end GGT
end GroupApproximation
