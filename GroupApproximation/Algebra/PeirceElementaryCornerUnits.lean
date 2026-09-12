import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsKappaProof
import GroupApproximation.Algebra.PeirceElementaryFactorization

/-!
# The printed route reaches the printed destination

`non_mf_groups_exist.tex`, proof of `thm:mf-quotient-units`, item (a) and the
paragraph that consumes it.

Item (a) factors a unit as `u = gvh` with `g` and `h` products of elementary
matrices of the twisted `m × m` matrix ring, and the paragraph after it
concludes `u ≡ v` modulo `N`.  On the tree those were two different objects:
`Algebra/PeirceElementaryFactorization.printedItemA` produces
`FactorsThrough (peirceElementarySubgroup e) u v`, while
`MFQuotientUnits.AGPMenalMoncasiReduction` asks for
`u * v⁻¹ ∈ cornerUnitSubgroup R`, and nothing related the two subgroups.  This
module relates them:

    `peirceElementarySubgroup e ≤ cornerUnitSubgroup R`.

With it the printed step is three lines, because `cornerUnitSubgroup` is
normal: `u = g * v * h` gives `u * v⁻¹ = g * (v * h * v⁻¹)`.

## Nothing here was load-bearing

`agpMenalMoncasiReduction` is already proved outright, by a two-index Peirce
route that never builds the `m`-block decomposition.  So this module closes a
*fidelity* gap, not a debt: it shows the printed argument arrives where the
printed proof says it does, rather than making any endpoint less conditional.

## The two cases, and why the second needs the printed Steinberg identity

A Peirce-elementary unit is `1 + x` with `e i * x = x`, `x * e j = x`, `i ≠ j`.

* **Both indices off `last`.**  Item (a) has `e i` and `e j` equivalent to each
  other there, and — this is the hypothesis `hone` below — to `1`.  Two
  orthogonal idempotents equivalent to `1` are a `2 × 2` matrix-unit system, so
  `x = s i * (t i * x * s j) * t j` is the image of an elementary matrix under
  `matrixCornerUnitHom`, and `elementaryRange_le_cornerUnitSubgroup` puts it in
  `cornerUnitSubgroup R`.
* **One index is `last`.**  There `e last` is equivalent only to `f ≤ e i₀`, so
  the matrix-unit system is unavailable and the first case does not apply.  The
  printed proof's own device closes it: `e_{im}(x) = [e_{ij}(1), e_{jm}(x)]`
  and `e_{mj}(x) = [e_{mi}(x), e_{ij}(1)]` write a last-row or last-column root
  as a commutator with one factor off `last`, and a normal subgroup containing
  that factor contains the commutator.  `Peirce.oneAddIn_product` is that
  calculation, and it takes the containment on *either* side, which is what the
  two displays need.

The last-block case needs a *third* index, to play the printed `j` in
`e_{im}(x) = [e_{ij}(1), e_{jm}(x)]`.  That costs `3 ≤ m`, which is weaker than
the printed `m ≥ 4`, so the statements below are stronger than the printed
sentence rather than a restriction of it.  Nothing here uses the fourth block.

## The hypothesis `hone`, and where it comes from

`PrintedItemA` states that the blocks off `last` are pairwise equivalent, not
that they are equivalent to `1`.  The decomposition it *builds* has the stronger
property — its blocks come from `exists_orthogonal_unit_family`, whose whole
content is that each member is equivalent to `1` — but the existential does not
expose it, so it is taken as a hypothesis here and discharged by the caller.
`peirceBlocks_le_cornerUnitSubgroup` discharges it for exactly the family
`printedItemA` builds, where it is free.
-/

namespace GroupApproximation
namespace MFQuotientUnits

open Peirce

/-! ## Coordinates from a family of idempotents equivalent to the unit -/

section Coordinates

variable {R : Type} [Ring R] [Countable R]

omit [Countable R] in
/-- Orthogonal idempotents each equivalent to `1` form a matrix-unit system.
Same construction as `KappaProof.exists_coordinates`, but for a family given in
advance rather than one chosen by the proof. -/
theorem exists_coordinates_of_unitFamily {n : ℕ} (e : Fin n → R)
    (hidem : ∀ i, IsIdempotentElem (e i))
    (horth : ∀ i j : Fin n, i ≠ j → e i * e j = 0)
    (hone : ∀ i, IsEquivalentIdempotent R (e i) 1) :
    ∃ s t : Fin n → R, (∀ i, t i * s i = 1) ∧
      (∀ i j : Fin n, i ≠ j → t i * s j = 0) ∧ ∀ i, s i * t i = e i := by
  have hc : ∀ i : Fin n, ∃ s t : R, t * s = 1 ∧ s * t = e i := by
    intro i
    obtain ⟨s, t, hts, hst, -, -, -, -⟩ :=
      exists_normalized_isometry IsIdempotentElem.one (hidem i) (one_mul _)
        (mul_one _) (hone i).symm
    exact ⟨s, t, hts, hst⟩
  choose s t hts hst using hc
  refine ⟨s, t, hts, ?_, hst⟩
  intro i j hij
  have hs : e j * s j = s j := by rw [← hst j, mul_assoc, hts j, mul_one]
  have ht : t i * e i = t i := by rw [← hst i, ← mul_assoc, hts i, one_mul]
  calc t i * s j = (t i * e i) * (e j * s j) := by rw [ht, hs]
    _ = t i * (e i * e j) * s j := by noncomm_ring
    _ = 0 := by rw [horth i j hij]; simp

/-- **A single elementary root at a matrix-unit system is a corner unit.**  It
is the image of one elementary matrix under `matrixCornerUnitHom`, and
`elementaryRange_le_cornerUnitSubgroup` puts that image in
`cornerUnitSubgroup R`. -/
theorem oneAddIn_cornerUnitSubgroup_of_coordinates
    (hR : IsPurelyInfiniteSimpleRing R) {n : ℕ} (hn : 2 ≤ n) {s t : Fin n → R}
    (hts : ∀ i, t i * s i = 1) (hcross : ∀ i j : Fin n, i ≠ j → t i * s j = 0)
    {i j : Fin n} (hij : i ≠ j) (c : R) :
    OneAddIn (cornerUnitSubgroup R) (s i * c * t j) := by
  refine ⟨matrixCornerUnitHom s t hts hcross (elementaryUnit i j hij c), ?_, ?_⟩
  · refine elementaryRange_le_cornerUnitSubgroup hR hn
      ((matrixCornerUnitHom s t hts hcross).comp
        (elementaryGroup (Fin n) R).subtype) ?_
    exact ⟨⟨elementaryUnit i j hij c, elementaryUnit_mem i j hij c⟩, rfl⟩
  · rw [coe_matrixCornerUnitHom]
    show 1 - matrixWitnessSum s t
        + matrixEmbed s t (1 + Matrix.single i j c) = 1 + s i * c * t j
    rw [matrixEmbed_add, matrixEmbed_one, KappaProof.matrixEmbed_single]
    abel

/-- **A Peirce root between two idempotents equivalent to `1` is a corner
unit.** -/
theorem oneAddIn_cornerUnitSubgroup_of_unitPair
    (hR : IsPurelyInfiniteSimpleRing R) {p q : R}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (hpq : p * q = 0) (hqp : q * p = 0)
    (hp1 : IsEquivalentIdempotent R p 1) (hq1 : IsEquivalentIdempotent R q 1)
    {x : R} (hpx : p * x = x) (hxq : x * q = x) :
    OneAddIn (cornerUnitSubgroup R) x := by
  classical
  have hidem : ∀ i : Fin 2, IsIdempotentElem (![p, q] i) := by
    intro i
    fin_cases i
    · simpa using hp
    · simpa using hq
  have horth : ∀ i j : Fin 2, i ≠ j → ![p, q] i * ![p, q] j = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | simpa using hpq
        | simpa using hqp
  have hone : ∀ i : Fin 2, IsEquivalentIdempotent R (![p, q] i) 1 := by
    intro i
    fin_cases i
    · simpa using hp1
    · simpa using hq1
  obtain ⟨s, t, hts, hcross, hst⟩ :=
    exists_coordinates_of_unitFamily ![p, q] hidem horth hone
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hs0 : s 0 * t 0 = p := by
    have := hst 0
    simpa using this
  have hs1 : s 1 * t 1 = q := by
    have := hst 1
    simpa using this
  have hx : s 0 * (t 0 * x * s 1) * t 1 = x := by
    calc s 0 * (t 0 * x * s 1) * t 1 = (s 0 * t 0) * x * (s 1 * t 1) := by
          noncomm_ring
      _ = p * x * q := by rw [hs0, hs1]
      _ = x := by rw [hpx, hxq]
  rw [← hx]
  exact oneAddIn_cornerUnitSubgroup_of_coordinates hR (le_refl 2) hts hcross h01 _

end Coordinates

/-! ## A third index -/

theorem exists_ne_two {m : ℕ} (hm : 3 ≤ m) (a b : Fin m) :
    ∃ c : Fin m, c ≠ a ∧ c ≠ b := by
  classical
  have hle : ({a, b} : Finset (Fin m)).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  have hne : ({a, b} : Finset (Fin m)) ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ, Fintype.card_fin] at hle
    omega
  obtain ⟨c, -, hc⟩ :=
    Finset.exists_of_ssubset (Finset.ssubset_univ_iff.mpr hne)
  exact ⟨c, fun h => hc (by simp [h]), fun h => hc (by simp [h])⟩

/-! ## The bridge -/

section Bridge

variable {R : Type} [Ring R] [Countable R]

/-- **Every Peirce-elementary unit of an item-(a) decomposition is a corner
unit.**

The hypotheses are item (a)'s, with `hone` added: the blocks off `last` are
equivalent to `1`, not merely to each other.  See the module docstring for why
that is not automatic from the printed sentence and where it comes from. -/
theorem oneAddIn_cornerUnitSubgroup_of_itemA
    (hR : IsPurelyInfiniteSimpleRing R) {m : ℕ} (hm : 3 ≤ m) {e : Fin m → R}
    {last : Fin m} (hidem : ∀ i, IsIdempotentElem (e i))
    (horth : ∀ i j : Fin m, i ≠ j → e i * e j = 0)
    (hone : ∀ i, i ≠ last → IsEquivalentIdempotent R (e i) 1)
    {i j : Fin m} (hij : i ≠ j) {x : R} (hix : e i * x = x) (hxj : x * e j = x) :
    OneAddIn (cornerUnitSubgroup R) x := by
  classical
  by_cases hil : i = last
  · -- Last row.  Printed: `e_{mj}(x) = [e_{mk}(x), e_{kj}(1)]`.
    subst hil
    have hjl : j ≠ i := fun h => hij h.symm
    obtain ⟨k, hkj, hkl⟩ := exists_ne_two hm j i
    have hequiv : IsEquivalentIdempotent R (e k) (e j) :=
      IsEquivalentIdempotent.trans (hidem k) (hidem j) (hone k hkl)
        (hone j hjl).symm
    obtain ⟨u, v, huv, hvu, hku, huj, hjv, hvk⟩ :=
      exists_normalized_equivalence (hidem k) (hidem j) hequiv
    have hvx : v * x = 0 := by
      calc v * x = (v * e k) * (e i * x) := by rw [hvk, hix]
        _ = v * (e k * e i) * x := by noncomm_ring
        _ = 0 := by rw [horth k i hkl]; simp
    have hux : u * x = 0 := by
      calc u * x = (u * e j) * (e i * x) := by rw [huj, hix]
        _ = u * (e j * e i) * x := by noncomm_ring
        _ = 0 := by rw [horth j i hjl]; simp
    have haa : (x * v) * (x * v) = 0 := by
      calc (x * v) * (x * v) = x * (v * x) * v := by noncomm_ring
        _ = 0 := by rw [hvx]; simp
    have hbb : u * u = 0 := by
      calc u * u = (u * e j) * (e k * u) := by rw [huj, hku]
        _ = u * (e j * e k) * u := by noncomm_ring
        _ = 0 := by rw [horth j k (Ne.symm hkj)]; simp
    have hba : u * (x * v) = 0 := by rw [← mul_assoc, hux, zero_mul]
    have hprod : (x * v) * u = x := by
      calc (x * v) * u = x * (v * u) := by noncomm_ring
        _ = x * e j := by rw [hvu]
        _ = x := hxj
    have hu : OneAddIn (cornerUnitSubgroup R) u :=
      oneAddIn_cornerUnitSubgroup_of_unitPair hR (hidem k) (hidem j)
        (horth k j hkj) (horth j k (Ne.symm hkj)) (hone k hkl) (hone j hjl)
        hku huj
    rw [← hprod]
    exact oneAddIn_product haa hbb hba (Or.inr hu)
  · by_cases hjl : j = last
    · -- Last column.  Printed: `e_{im}(x) = [e_{ik}(1), e_{km}(x)]`.
      subst hjl
      obtain ⟨k, hki, hkl⟩ := exists_ne_two hm i j
      have hequiv : IsEquivalentIdempotent R (e i) (e k) :=
        IsEquivalentIdempotent.trans (hidem i) (hidem k) (hone i hil)
          (hone k hkl).symm
      obtain ⟨u, v, huv, hvu, hiu, huk, hkv, hvi⟩ :=
        exists_normalized_equivalence (hidem i) (hidem k) hequiv
      have hxv : x * v = 0 := by
        calc x * v = (x * e j) * (e k * v) := by rw [hxj, hkv]
          _ = x * (e j * e k) * v := by noncomm_ring
          _ = 0 := by rw [horth j k (Ne.symm hkl)]; simp
      have hxu : x * u = 0 := by
        calc x * u = (x * e j) * (e i * u) := by rw [hxj, hiu]
          _ = x * (e j * e i) * u := by noncomm_ring
          _ = 0 := by rw [horth j i (Ne.symm hil)]; simp
      have haa : u * u = 0 := by
        calc u * u = (u * e k) * (e i * u) := by rw [huk, hiu]
          _ = u * (e k * e i) * u := by noncomm_ring
          _ = 0 := by rw [horth k i hki]; simp
      have hbb : (v * x) * (v * x) = 0 := by
        calc (v * x) * (v * x) = v * (x * v) * x := by noncomm_ring
          _ = 0 := by rw [hxv]; simp
      have hba : (v * x) * u = 0 := by rw [mul_assoc, hxu, mul_zero]
      have hprod : u * (v * x) = x := by
        calc u * (v * x) = (u * v) * x := by noncomm_ring
          _ = e i * x := by rw [huv]
          _ = x := hix
      have hu : OneAddIn (cornerUnitSubgroup R) u :=
        oneAddIn_cornerUnitSubgroup_of_unitPair hR (hidem i) (hidem k)
          (horth i k (Ne.symm hki)) (horth k i hki) (hone i hil) (hone k hkl)
          hiu huk
      rw [← hprod]
      exact oneAddIn_product haa hbb hba (Or.inl hu)
    · -- Both indices off `last`.
      exact oneAddIn_cornerUnitSubgroup_of_unitPair hR (hidem i) (hidem j)
        (horth i j hij) (horth j i (fun h => hij h.symm)) (hone i hil)
        (hone j hjl) hix hxj

/-- **The bridge.**  Every product of elementary matrices of the twisted matrix
ring of item (a) is a corner unit. -/
theorem peirceElementarySubgroup_le_cornerUnitSubgroup
    (hR : IsPurelyInfiniteSimpleRing R) {m : ℕ} (hm : 3 ≤ m) {e : Fin m → R}
    {last : Fin m} (hidem : ∀ i, IsIdempotentElem (e i))
    (horth : ∀ i j : Fin m, i ≠ j → e i * e j = 0)
    (hone : ∀ i, i ≠ last → IsEquivalentIdempotent R (e i) 1) :
    peirceElementarySubgroup e ≤ cornerUnitSubgroup R := by
  rw [peirceElementarySubgroup, Subgroup.closure_le]
  rintro w ⟨i, j, x, hij, hix, hxj, hw⟩
  exact (oneAddIn_cornerUnitSubgroup_of_itemA hR hm hidem horth hone hij hix
    hxj).mem w hw

/-- **The printed route reaches the printed destination.**

Item (a) gives `u = gvh` with `g` and `h` products of elementary matrices; the
printed proof then says `u ≡ v` modulo `N`.  Given the bridge that is three
lines, because `cornerUnitSubgroup` is normal:
`u * v⁻¹ = g * (v * h * v⁻¹)`. -/
theorem factorsThrough_mul_inv_mem_cornerUnitSubgroup
    (hR : IsPurelyInfiniteSimpleRing R) {m : ℕ} (hm : 3 ≤ m) {e : Fin m → R}
    {last : Fin m} (hidem : ∀ i, IsIdempotentElem (e i))
    (horth : ∀ i j : Fin m, i ≠ j → e i * e j = 0)
    (hone : ∀ i, i ≠ last → IsEquivalentIdempotent R (e i) 1)
    {u v : Rˣ} (hfac : FactorsThrough (peirceElementarySubgroup e) u v) :
    u * v⁻¹ ∈ cornerUnitSubgroup R := by
  obtain ⟨g, h, hg, hh, huvh⟩ := hfac
  have hle :=
    peirceElementarySubgroup_le_cornerUnitSubgroup hR hm hidem horth hone
      (last := last)
  have hconj : v * h * v⁻¹ ∈ cornerUnitSubgroup R :=
    (cornerUnitSubgroup_normal R).conj_mem _ (hle hh) v
  have hsplit : u * v⁻¹ = g * (v * h * v⁻¹) := by rw [huvh]; group
  rw [hsplit]
  exact (cornerUnitSubgroup R).mul_mem (hle hg) hconj

/-- **The hypothesis `hone` is free at the family `printedItemA` builds.**

`Algebra/PeirceElementaryFactorization.lean` takes its blocks from
`exists_orthogonal_unit_family`, whose members are equivalent to `1`, and adds
the remainder as the last block.  So the bridge applies to that decomposition
with nothing to check. -/
theorem peirceBlocks_le_cornerUnitSubgroup
    (hR : IsPurelyInfiniteSimpleRing R) {n : ℕ} (hn : 2 ≤ n) (r : Fin n → R)
    (hridem : ∀ i, IsIdempotentElem (r i))
    (hrorth : ∀ i j : Fin n, i ≠ j → r i * r j = 0)
    (hrequiv : ∀ i, IsEquivalentIdempotent R (r i) 1) :
    peirceElementarySubgroup (peirceBlocks r) ≤ cornerUnitSubgroup R := by
  refine peirceElementarySubgroup_le_cornerUnitSubgroup hR (m := n + 1)
    (by omega) (peirceBlocks_isIdempotentElem r hridem hrorth)
    (peirceBlocks_orthogonal r hridem hrorth) (last := Fin.last n) ?_
  intro i hi
  obtain ⟨a, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
  rw [peirceBlocks_castSucc]
  exact hrequiv a

end Bridge

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.exists_coordinates_of_unitFamily
#audit_axioms
  GroupApproximation.MFQuotientUnits.oneAddIn_cornerUnitSubgroup_of_coordinates
#audit_axioms
  GroupApproximation.MFQuotientUnits.oneAddIn_cornerUnitSubgroup_of_unitPair
#audit_axioms GroupApproximation.MFQuotientUnits.exists_ne_two
#audit_axioms GroupApproximation.MFQuotientUnits.oneAddIn_cornerUnitSubgroup_of_itemA
#audit_axioms
  GroupApproximation.MFQuotientUnits.peirceElementarySubgroup_le_cornerUnitSubgroup
#audit_axioms
  GroupApproximation.MFQuotientUnits.factorsThrough_mul_inv_mem_cornerUnitSubgroup
#audit_axioms GroupApproximation.MFQuotientUnits.peirceBlocks_le_cornerUnitSubgroup
