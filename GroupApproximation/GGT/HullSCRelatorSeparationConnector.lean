import GroupApproximation.GGT.HullSCRelatorSeparationSpacing

/-!
# The connecting element is bounded by the word, not by the polygon

Osin's isolated-component argument names the element of `H` joining two
connected components -- it is `(y · a₋)⁻¹ · a'₋` for the two initial vertices --
but it does not bound it, and in the deep case no bound is available from that
argument.  A bound is nevertheless what Olshanskii's conclusion needs, since an
unbounded element of `H` relates the two runs by nothing at all.

It comes from the *word* instead, and this module supplies it.

For the first components of the two matched prefixes the initial vertices are
values of prefixes made of **base letters only**: Hull's relator is
`p · h^{m₁} ⋯ h^{m_k}`, its `H`-letters form a single run
(`GGT/HullSCRelatorSeparationComponent.lean`), so the cyclic word has exactly one
maximal block of base letters, of length `|p|`, and everything preceding the
first run of any member of the symmetrized closure lies in that block.  So both
initial vertices have base-length at most `|p|`, the connector is
`c⁻¹ · y⁻¹ · c'` with `|c|, |c'| ≤ |p|` and `|y| ≤ eps`, and
`mem_relBall_of_connector` puts it in the relative ball of radius
`2|p| + eps`, which is finite.

Nothing about that is geometric, and the order of choice works: `|p|` is fixed
by the spacing requirement, which depends only on the quasi-geodesicity
constants of `E` and not on the length of the relator
(`HullSC.exists_long_base_spelling` makes it free), so `relBall (2|p| + eps)` is
a fixed finite set against which the exponents are then chosen.

So `hquad` should name the connector and say nothing about its size.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section Connector

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A word of base letters spells an element of at most that base-length.**

The initial vertex of the first component of a member of the symmetrized closure
is such a value, and the relator has only `|p|` base letters, so the bound is
`|p|`. -/
theorem wordNorm_listVal_le {D : GGT.RelGenSet G Λ}
    (hbase : IsSymmetricGeneratingSet D.base) {u : List (GGT.RelLetter G Λ)}
    (hu : ∀ a ∈ u, ∃ g, g ∈ D.base ∧ a = GGT.RelLetter.base g) :
    wordNorm D.base (GGT.RelLetter.listVal u) ≤ u.length := by
  induction u with
  | nil =>
      rw [GGT.RelLetter.listVal_nil, wordNorm_one]
      exact Nat.zero_le _
  | cons a t ih =>
      obtain ⟨g, hg, rfl⟩ := hu a (List.mem_cons.mpr (Or.inl rfl))
      rw [RelWord.listVal_cons, List.length_cons]
      have h1 : wordNorm D.base
          ((GGT.RelLetter.base g : GGT.RelLetter G Λ).val
            * GGT.RelLetter.listVal t)
          ≤ wordNorm D.base (GGT.RelLetter.base g : GGT.RelLetter G Λ).val
            + wordNorm D.base (GGT.RelLetter.listVal t) :=
        wordNorm_mul_le hbase _ _
      have h2 : wordNorm D.base
          (GGT.RelLetter.base g : GGT.RelLetter G Λ).val ≤ 1 :=
        wordNorm_le_one_of_mem hg
      have h3 := ih (fun b hb => hu b (List.mem_cons.mpr (Or.inr hb)))
      omega

/-- **The connecting element of two matched components is shallow.**

It is `c⁻¹ · y⁻¹ · c'` for the two initial vertices `c`, `c'` and the
translation `y`, so its base-length is at most `|c| + |y| + |c'|`; and it lies
in the family, so `mem_relBall_of_wordNorm_le` turns that into membership of the
relative ball.

This is the bound the isolated-component argument does not give and does not
have to: it is a statement about the word, and it holds however deep the
components are. -/
theorem mem_relBall_of_connector {D : GGT.RelGenSet G Λ}
    (hbase : IsSymmetricGeneratingSet D.base) {lam : Λ} {h y c c' : G}
    {n m : ℕ} (hh : h ∈ D.fam lam) (heq : h = c⁻¹ * y⁻¹ * c')
    (hc : wordNorm D.base c ≤ n) (hy : wordNorm D.base y ≤ m)
    (hc' : wordNorm D.base c' ≤ n) : h ∈ D.relBall lam (n + m + n) := by
  refine mem_relBall_of_wordNorm_le hbase hh ?_
  rw [heq]
  have h1 := wordNorm_mul_le hbase (c⁻¹ * y⁻¹) c'
  have h2 := wordNorm_mul_le hbase c⁻¹ y⁻¹
  have h3 : wordNorm D.base c⁻¹ = wordNorm D.base c := wordNorm_inv hbase c
  have h4 : wordNorm D.base y⁻¹ = wordNorm D.base y := wordNorm_inv hbase y
  omega

end Connector

/-! ## The bound in the form the estimate uses it -/

/-- **The connector of the first matched components lies in a fixed finite
ball.**

`c` and `c'` are the values of the base-letter prefixes preceding the two first
components, each of length at most `|p|`; `y` is the translation, of base-length
at most `eps`.  So the connector lies in `relBall () (2|p| + eps)`, a set that
does not grow with the relator: `|p|` is fixed by the spacing requirement before
the exponents are chosen. -/
theorem mem_relBall_of_firstConnector {G : Type u} [Group G]
    {A : HullGeneratingSet G} {N : Subgroup G} (E : HypEmbeddedCore A N)
    {P eps : ℕ} {h y : G} {u u' : List (GGT.RelLetter G Unit)}
    (hu : ∀ a ∈ u, ∃ g, g ∈ E.rel.base ∧ a = GGT.RelLetter.base g)
    (hu' : ∀ a ∈ u', ∃ g, g ∈ E.rel.base ∧ a = GGT.RelLetter.base g)
    (hlen : u.length ≤ P) (hlen' : u'.length ≤ P)
    (hy : wordNorm E.rel.base y ≤ eps) (hh : h ∈ E.rel.fam ())
    (heq : h = (GGT.RelLetter.listVal u)⁻¹ * y⁻¹ * GGT.RelLetter.listVal u') :
    h ∈ E.rel.relBall () (P + eps + P) := by
  have hbase := isSymmetricGeneratingSet_base E
  refine mem_relBall_of_connector hbase hh heq ?_ hy ?_
  · exact le_trans (wordNorm_listVal_le hbase hu) hlen
  · exact le_trans (wordNorm_listVal_le hbase hu') hlen'

end HullSC
end GroupApproximation
