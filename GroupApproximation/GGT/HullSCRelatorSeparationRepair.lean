import GroupApproximation.GGT.HullSCRelatorSeparationValues

/-!
# Hull's §6 with Olshanskii's exclusion clause put back

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, Groups
Geom. Dyn. 10 (2016) 1077-1119, §6, after Olshanskii.

`HullSC.RelWord.IsPiece` requires the second member of the family to be a
*different* word, `v' ≠ v`; that is Olshanskii's exclusion clause and it is
already in the definition.  `HullSC.RelWord.pieces_small_of_longMatch`
destructures a piece and drops the clause, so the hypothesis it asks for -- and
`HullSC.RelatorChoice` and `HullSC.RelatorSeparation` after it -- also
quantifies over the diagonal `w' = w`, where the statement degenerates into the
demand that every `y` of the `eps`-ball fixing the relator's value from both
sides centralize it.  `GGT/HullSCRelatorSeparationRefuted.lean` refutes that
demand.

This module runs the same reduction with the clause kept.

* `RelWord.pieces_small_of_longMatch_ne` -- the piece bound from a length bound,
  with `w' ≠ w` passed on to the estimate.  The proof is the proof of
  `pieces_small_of_longMatch`; the only change is that the clause is used
  instead of discarded.
* `RelWord.isSmallCancellation_symmetrized_of_longMatch_ne` -- all six clauses
  of `C(eps, mu, rho)` for the symmetrized closure of one relator, five from
  `RelWord.isSmallCancellation_symmetrized` and the sixth from the line above.
* `hullRelatorStatement_of_separationNe` -- **`HullSC.HullRelatorStatement` from
  the corrected separation**, with the relator written down as a base spelling
  of `t⁻¹` followed by deep powers of `E.lox`.

The last one goes straight to `HullRelatorStatement` rather than through
`HullSC.RelatorChoice`, because `RelatorChoice` records the match clause in the
same uncorrected form: `relatorChoice_of_relatorSeparation` passes the estimate
through untouched, so a corrected estimate does not produce it.  Nothing is lost
-- `hullTheorem51_of_relator_of_quotient` consumes `HullRelatorStatement`, not
`RelatorChoice`.

The bookkeeping is the bookkeeping of `relatorChoice_of_relatorSeparation`:
`u = E.lox^{Σ mᵢ}` lies in `E.H ≤ N`, admissibility and depth come from the
letters of the relator one at a time, the length is whatever the exponent list
gives, and `mu` is met by taking the relator long, the estimate having produced
its constant `B` before the length.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

namespace RelWord

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The piece bound from a length bound, with Olshanskii's exclusion clause
kept.**

If every `eps`-match of a prefix longer than `B` *between two different members*
of the family is a global translation, then every `eps`-piece is shorter than
`B`, and `B < mu |v|` finishes.  The extra hypothesis `w' ≠ w` is exactly the
clause `RelWord.IsPiece` carries, so nothing is assumed that a piece does not
supply.

This is `pieces_small_of_longMatch` with the clause used rather than
discarded. -/
theorem pieces_small_of_longMatch_ne {D : GGT.RelGenSet G Λ}
    {v : List (GGT.RelLetter G Λ)} {eps : ℕ} {mu : ℝ} {B : ℕ}
    (hmatch : ∀ w w' u u' : List (GGT.RelLetter G Λ), Sym v w → Sym v w' →
      w' ≠ w → (∃ s, w = u ++ s) → (∃ s', w' = u' ++ s') → B < u.length →
      ∀ y z : G, wordNorm D.base y ≤ eps → wordNorm D.base z ≤ eps →
        GGT.RelLetter.listVal u' = y * GGT.RelLetter.listVal u * z →
          GGT.RelLetter.listVal w'
            = y * GGT.RelLetter.listVal w * y⁻¹)
    (hB : (B : ℝ) < mu * v.length) :
    ∀ u w : List (GGT.RelLetter G Λ), IsPiece D (symmetrized v) eps u w →
      (u.length : ℝ) < mu * w.length := by
  intro u w hp
  obtain ⟨hw, hpre, w', hw', hne, u', s', hw'eq, y, z, hy, hz, hval, hexcl⟩ := hp
  have hsw : Sym v w := mem_symmetrized.mp hw
  have hsw' : Sym v w' := mem_symmetrized.mp hw'
  have hlen : (w.length : ℝ) = (v.length : ℝ) := by
    rw [Sym.length_eq hsw]
  by_cases hbig : B < u.length
  · exact absurd
      (hmatch w w' u u' hsw hsw' hne hpre ⟨s', hw'eq⟩ hbig y z hy hz hval) hexcl
  · have h1 : (u.length : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast Nat.not_lt.mp hbig
    rw [hlen]
    linarith [h1, hB]

/-- **`C(eps, mu, rho)` for the symmetrized closure of one relator**, from the
corrected estimate.  Five clauses are
`RelWord.isSmallCancellation_symmetrized` and the sixth is
`pieces_small_of_longMatch_ne`. -/
theorem isSmallCancellation_symmetrized_of_longMatch_ne
    {D : GGT.RelGenSet G Λ} {v : List (GGT.RelLetter G Λ)} {eps rho : ℕ}
    {mu : ℝ} {B : ℕ}
    (hbase : ∀ g ∈ D.base, g⁻¹ ∈ D.base)
    (hadm : ∀ a ∈ v, D.IsLetter a)
    (hlong : rho ≤ v.length)
    (hdeep : ∀ a ∈ v, ∀ lam : Λ, GGT.RelLetter.IsCompOf lam a →
      a.val ∉ D.relBall lam rho ∧ (a.val)⁻¹ ∉ D.relBall lam rho)
    (hmatch : ∀ w w' u u' : List (GGT.RelLetter G Λ), Sym v w → Sym v w' →
      w' ≠ w → (∃ s, w = u ++ s) → (∃ s', w' = u' ++ s') → B < u.length →
      ∀ y z : G, wordNorm D.base y ≤ eps → wordNorm D.base z ≤ eps →
        GGT.RelLetter.listVal u' = y * GGT.RelLetter.listVal u * z →
          GGT.RelLetter.listVal w'
            = y * GGT.RelLetter.listVal w * y⁻¹)
    (hB : (B : ℝ) < mu * v.length) :
    IsSmallCancellation D (symmetrized v) eps mu rho :=
  isSmallCancellation_symmetrized hbase hadm hlong hdeep
    (pieces_small_of_longMatch_ne hmatch hB)

end RelWord

/-! ## Hull's §6 from the corrected separation -/

/-- **Hull's §6, from Olshanskii's separation with the exclusion clause.**

The hypothesis is `HullSC.RelatorSeparation` with `w' ≠ w` restored:

> Let `G` be acylindrically hyperbolic with Hull's alphabet `A`, let `N` be
> suitable, let `H ≤ N` be hyperbolically embedded with the loxodromic element
> `h`, let `t ∈ G` and let `eps, rho` be given.  Then there is a constant `B`
> such that for every length `L` there are a base spelling `p` of `t⁻¹` and at
> least `L` deep exponents `m₁, …, m_k` for which every `eps`-match of a prefix
> longer than `B`, between **two different** members of the symmetrized closure
> of `p · h^{m₁} ⋯ h^{m_k}`, is a global translation of the member.

The conclusion is `HullSC.HullRelatorStatement`, which is what
`HullSC.hullTheorem51_of_relator_of_quotient` consumes.

Everything except the separation is discharged here and none of it is a choice:
`u = E.lox^{Σ mᵢ}` lies in `E.H`, hence in `N`, so the relator spells `t⁻¹ u`;
the base letters of `p` are letters of `A` and the `H`-letters are powers of an
element of `E.H`, so the relator is admissible; the depth clause is the clause
the exponents were chosen for; the length is at least `rho` because the exponent
list is at least `max rho n` long; and `mu` is met because the estimate produced
`B` before the length, so the relator can be taken longer than `B / mu`.

`HullSC.exists_base_spelling` and `HullSC.exists_deep_relator_exponents` prove
that the clauses other than the separation can always be met, so the hypothesis
is a statement about matches and not a bundle hiding an unsatisfiable side
condition. -/
theorem hullRelatorStatement_of_separationNe
    (h : ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
      (E : HypEmbeddedCore A N), Suitable A.alphabet N → ∀ (t : G) (eps rho : ℕ),
        ∃ B : ℕ, ∀ L : ℕ, ∃ (p : List G) (ms : List ℕ),
          (∀ g ∈ p, g ∈ E.rel.base) ∧ p.prod = t⁻¹ ∧ L ≤ ms.length ∧
            (∀ m ∈ ms, E.lox ^ m ∉ E.rel.relBall () rho ∧
              (E.lox ^ m)⁻¹ ∉ E.rel.relBall () rho) ∧
            ∀ w w' u₀ u₀' : List (GGT.RelLetter G Unit),
              RelWord.Sym (relatorWord p E.lox ms) w →
                RelWord.Sym (relatorWord p E.lox ms) w' → w' ≠ w →
                  (∃ s, w = u₀ ++ s) → (∃ s', w' = u₀' ++ s') → B < u₀.length →
                    ∀ y z : G, wordNorm E.rel.base y ≤ eps →
                      wordNorm E.rel.base z ≤ eps →
                        GGT.RelLetter.listVal u₀'
                            = y * GGT.RelLetter.listVal u₀ * z →
                          GGT.RelLetter.listVal w'
                            = y * GGT.RelLetter.listVal w * y⁻¹) :
    HullRelatorStatement.{u} := by
  intro G _ A N E hN t eps rho mu hmu
  obtain ⟨B, hB⟩ := h A N E hN t eps rho
  obtain ⟨n, hn⟩ := exists_nat_gt ((B : ℝ) / mu)
  obtain ⟨p, ms, hpbase, hpprod, hlen, hdeep, hsep⟩ := hB (max rho n)
  have h1 : (B : ℝ) < (n : ℝ) * mu := by
    rw [div_lt_iff₀ hmu] at hn
    exact hn
  have h2 : (n : ℝ) ≤ ((max rho n : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_right rho n
  have hBL : (B : ℝ) < mu * ((max rho n : ℕ) : ℝ) := by
    have h3 : (n : ℝ) * mu ≤ ((max rho n : ℕ) : ℝ) * mu :=
      mul_le_mul_of_nonneg_right h2 (le_of_lt hmu)
    calc (B : ℝ) < (n : ℝ) * mu := h1
      _ ≤ ((max rho n : ℕ) : ℝ) * mu := h3
      _ = mu * ((max rho n : ℕ) : ℝ) := mul_comm _ _
  have hlenv : max rho n ≤ (relatorWord p E.lox ms).length := by
    rw [length_relatorWord]
    omega
  have hBv : (B : ℝ) < mu * ((relatorWord p E.lox ms).length : ℝ) := by
    have h4 : ((max rho n : ℕ) : ℝ)
        ≤ ((relatorWord p E.lox ms).length : ℝ) := by
      exact_mod_cast hlenv
    have h5 : mu * ((max rho n : ℕ) : ℝ)
        ≤ mu * ((relatorWord p E.lox ms).length : ℝ) :=
      mul_le_mul_of_nonneg_left h4 (le_of_lt hmu)
    linarith [hBL, h5]
  have hbase : ∀ g ∈ E.rel.base, g⁻¹ ∈ E.rel.base := by
    intro g hg
    rw [E.base_eq] at hg ⊢
    exact A.alphabet.symmetricGenerating.inv_mem g hg
  refine ⟨E.lox ^ ms.sum, E.le (E.H.pow_mem E.lox_mem ms.sum),
    RelWord.symmetrized (relatorWord p E.lox ms),
    ⟨relatorWord p E.lox ms,
      RelWord.self_mem_symmetrized (relatorWord p E.lox ms), ?_⟩, ?_⟩
  · rw [listVal_relatorWord, hpprod]
  · refine RelWord.isSmallCancellation_symmetrized_of_longMatch_ne hbase ?_ ?_ ?_
      hsep hBv
    · intro x hx
      rcases mem_relatorWord hx with ⟨g, hg, rfl⟩ | ⟨m, _, rfl⟩
      · exact hpbase g hg
      · show E.lox ^ m ∈ E.rel.fam ()
        have hfam : E.rel.fam () = E.H := by rw [E.fam_eq]
        rw [hfam]
        exact E.H.pow_mem E.lox_mem m
    · have h6 : rho ≤ max rho n := Nat.le_max_left rho n
      omega
    · intro x hx lam hcomp
      rcases mem_relatorWord hx with ⟨g, _, rfl⟩ | ⟨m, hm, rfl⟩
      · exact False.elim hcomp
      · exact hdeep m hm

end HullSC
end GroupApproximation
