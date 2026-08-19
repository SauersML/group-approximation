import GroupApproximation.Analysis.ExactnessPermanence

/-!
# Property A is a local property: the increasing-union step, unconditionally

The manuscript's exactness paragraph cites Kirchberg--Wassermann for the step

> The `Q_n` increase with union the whole quotient, and a group with an
> increasing family of exact open subgroups whose union it is is itself exact
> \cite[Lemma~2.5]{KWExact} --- in a discrete group every subgroup is open ---
> so this quotient is exact.

This file proves that step, for `HasPropertyA` and with no hypothesis at all
beyond the ones in the sentence.  Nothing here is conditional and no literature
input is assumed: the whole argument is the observation below.

## Why the discrete case is elementary

`HasPropertyA` quantifies over a **finite** scale `R`.  Its closeness clause
compares the measures at two base points `g, h` only when `g⁻¹h ∈ R`.  So if
`R` happens to lie inside a subgroup `H`, the clause never compares base points
across different left cosets of `H`: `g⁻¹h ∈ H` says exactly that `gH = hH`.

That is the whole proof.  Choose one representative `rep g` in each left coset
and write `g = rep g · part g` with `part g ∈ H`.  Translate the subgroup's
measure system by `rep g`:

`weight g x = W.weight (part g) ((rep g)⁻¹ x)`  when `(rep g)⁻¹x ∈ H`, else `0`.

Mass and support transport verbatim, and the closeness clause is compared
inside a single coset, where the translation cancels and the estimate is
literally the subgroup's own.  No Følner set, no limit, no openness hypothesis
-- the openness in the printed citation is what makes the topological version
work, and in a discrete group it is vacuous, exactly as the manuscript says.

## Statements

* `nonempty_propertyAWitness_of_subgroup` -- a witness for `H` at a scale
  contained in `H` is a witness for `G` at that scale;
* `hasPropertyA_of_directed` -- **the printed lemma**: a group that is the union
  of a directed family of subgroups with property A has property A;
* `hasPropertyA_of_monotone` -- the same for an increasing chain, which is the
  shape the printed `Q_n` and the repository's mapping telescopes have;
* `hasPropertyA_of_forall_fg` -- property A is detected by finitely generated
  subgroups, and `hasPropertyA_of_forall_closure` is the form that needs no
  `Subgroup.FG` bookkeeping.

## What this does and does not discharge

It discharges one of the two Kirchberg--Wassermann citations in the exactness
paragraph, at group level, outright.  It does *not* touch the other one --- the
crossover from group exactness to exactness of the reduced `C*`-algebra --- nor
Guentner--Higson--Weinberger for the linear group.  Those remain exactly as
`ExactnessGroupSideEndpoint` records them, and this file deliberately adds no
hypothesis-carrying wrapper for either.
-/

namespace GroupApproximation
namespace PropertyALocality

open ExactnessPermanence

universe u

variable {G : Type u} [Group G]

/-! ## Coset coordinates -/

section Coordinates

variable (H : Subgroup G)

/-- A chosen representative of the left coset `gH`. -/
noncomputable def rep (g : G) : G := Quotient.out (QuotientGroup.mk g : G ⧸ H)

theorem mk_rep (g : G) :
    (QuotientGroup.mk (rep H g) : G ⧸ H) = QuotientGroup.mk g :=
  QuotientGroup.out_eq' _

theorem rep_inv_mul_mem (g : G) : (rep H g)⁻¹ * g ∈ H :=
  QuotientGroup.eq.mp (mk_rep H g)

/-- The `H`-coordinate of `g` relative to its coset representative. -/
noncomputable def part (g : G) : H := ⟨(rep H g)⁻¹ * g, rep_inv_mul_mem H g⟩

theorem part_coe (g : G) : ((part H g : H) : G) = (rep H g)⁻¹ * g := rfl

theorem rep_mul_part (g : G) : rep H g * ((part H g : H) : G) = g := by
  rw [part_coe, mul_inv_cancel_left]

/-- Base points at scale inside `H` share a coset, hence a representative.  This
is the one fact the whole file rests on. -/
theorem rep_eq_of_inv_mul_mem {g h : G} (hgh : g⁻¹ * h ∈ H) :
    rep H g = rep H h := by
  have hq : (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk h :=
    QuotientGroup.eq.mpr hgh
  unfold rep
  rw [hq]

end Coordinates

/-! ## The translated weight system -/

variable {H : Subgroup G} {RH : Finset H} {ε : ℝ}

/-- The subgroup's measure system, translated along coset representatives. -/
noncomputable def transportWeight (W : PropertyAWitness H RH ε) (g x : G) : ℝ :=
  @dite ℝ ((rep H g)⁻¹ * x ∈ H) (Classical.dec _)
    (fun hx ↦ W.weight (part H g) ⟨(rep H g)⁻¹ * x, hx⟩) (fun _ ↦ 0)

theorem transportWeight_of_mem (W : PropertyAWitness H RH ε) {g x : G}
    (hx : (rep H g)⁻¹ * x ∈ H) :
    transportWeight W g x = W.weight (part H g) ⟨(rep H g)⁻¹ * x, hx⟩ := by
  unfold transportWeight
  rw [dif_pos hx]

theorem transportWeight_of_notMem (W : PropertyAWitness H RH ε) {g x : G}
    (hx : (rep H g)⁻¹ * x ∉ H) : transportWeight W g x = 0 := by
  unfold transportWeight
  rw [dif_neg hx]

/-- On the coset of `g` the translated system *is* the subgroup's system. -/
theorem transportWeight_rep_mul (W : PropertyAWitness H RH ε) (g : G) (y : H) :
    transportWeight W g (rep H g * (y : G)) = W.weight (part H g) y := by
  have hx : (rep H g)⁻¹ * (rep H g * (y : G)) ∈ H := by
    rw [inv_mul_cancel_left]
    exact y.2
  rw [transportWeight_of_mem W hx]
  congr 1
  exact Subtype.ext (by rw [inv_mul_cancel_left])

/-- Everything the translated system charges sits on the coset of `g`, at a
point the subgroup's system charges. -/
theorem transportWeight_ne_zero (W : PropertyAWitness H RH ε) (g x : G)
    (hne : transportWeight W g x ≠ 0) :
    ∃ y : H, W.weight (part H g) y ≠ 0 ∧ x = rep H g * (y : G) := by
  by_cases hx : (rep H g)⁻¹ * x ∈ H
  · refine ⟨⟨(rep H g)⁻¹ * x, hx⟩, ?_, ?_⟩
    · rw [transportWeight_of_mem W hx] at hne
      exact hne
    · show x = rep H g * ((rep H g)⁻¹ * x)
      rw [mul_inv_cancel_left]
  · exact absurd (transportWeight_of_notMem W hx) hne

theorem transportWeight_nonneg (W : PropertyAWitness H RH ε) (g x : G) :
    0 ≤ transportWeight W g x := by
  by_cases hx : (rep H g)⁻¹ * x ∈ H
  · rw [transportWeight_of_mem W hx]
    exact W.weight_nonneg _ _
  · exact le_of_eq (transportWeight_of_notMem W hx).symm

/-! ## The transported witness -/

/-- **Property A transports from a subgroup that contains the scale.**

If every element of the finite scale `R` lies in `H`, then a property-A witness
for `H` gives one for `G` at that scale.  The closeness clause is the only place
the ambient group could intrude, and it never does: `g⁻¹h ∈ R ⊆ H` forces `g`
and `h` into a single left coset, where the translation cancels. -/
theorem nonempty_propertyAWitness_of_subgroup {H : Subgroup G}
    (hHA : HasPropertyA H) (R : Finset G) (hR : ∀ g ∈ R, g ∈ H)
    {ε : ℝ} (hε : 0 < ε) : Nonempty (PropertyAWitness G R ε) := by
  classical
  -- the same scale, read inside `H`
  obtain ⟨W⟩ :=
    hHA (R.attach.image fun x ↦ (⟨(x : G), hR (x : G) x.2⟩ : H)) ε hε
  have hRH : ∀ a ∈ R, ∃ y ∈ (R.attach.image fun x ↦ (⟨(x : G), hR (x : G) x.2⟩ : H)),
      ((y : H) : G) = a := by
    intro a ha
    exact ⟨⟨a, hR a ha⟩, Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_attach _ _, rfl⟩, rfl⟩
  refine ⟨{
    template := W.template.image fun y : H ↦ (y : G)
    weight := transportWeight W
    weight_nonneg := transportWeight_nonneg W
    weight_eq_zero := ?_
    weight_sum := ?_
    weight_close := ?_ }⟩
  · -- support
    intro g x hx
    by_contra hne
    obtain ⟨y, hy, rfl⟩ := transportWeight_ne_zero W g x hne
    refine hx (Finset.mem_image.mpr ⟨(part H g)⁻¹ * y, ?_, ?_⟩)
    · by_contra hcon
      exact hy (W.weight_eq_zero _ _ hcon)
    · show ((part H g : H) : G)⁻¹ * (y : G) = g⁻¹ * (rep H g * (y : G))
      rw [part_coe]
      group
  · -- total mass
    intro g
    rw [Finset.sum_image fun a _ b _ hab ↦ Subtype.ext hab]
    rw [← W.weight_sum (part H g)]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    have hrw : g * ((t : H) : G) = rep H g * ((part H g * t : H) : G) := by
      show g * (t : G) = rep H g * (((part H g : H) : G) * (t : G))
      rw [part_coe]
      group
    rw [hrw, transportWeight_rep_mul]
  · -- closeness
    intro g h hgh T hTg hTh
    obtain ⟨y0, hy0RH, hy0⟩ := hRH _ hgh
    have hmemH : g⁻¹ * h ∈ H := by
      rw [← hy0]
      exact y0.2
    have hrep : rep H g = rep H h := rep_eq_of_inv_mul_mem H hmemH
    have hpartcoe : (((part H g)⁻¹ * part H h : H) : G) = g⁻¹ * h := by
      show (((part H g : H) : G))⁻¹ * ((part H h : H) : G) = g⁻¹ * h
      rw [part_coe, part_coe, hrep]
      group
    have hpartRH : (part H g)⁻¹ * part H h ∈
        (R.attach.image fun x ↦ (⟨(x : G), hR (x : G) x.2⟩ : H)) := by
      have heq : (part H g)⁻¹ * part H h = y0 :=
        Subtype.ext (by rw [hpartcoe, hy0])
      rw [heq]
      exact hy0RH
    obtain ⟨T', hT'g, hT'h⟩ := W.exists_window (part H g) (part H h)
    have hclose := W.weight_close (part H g) (part H h) hpartRH T' hT'g hT'h
    -- the two evaluations on the common coset
    have hgval : ∀ y : H,
        transportWeight W g (rep H g * (y : G)) = W.weight (part H g) y :=
      transportWeight_rep_mul W g
    have hhval : ∀ y : H,
        transportWeight W h (rep H g * (y : G)) = W.weight (part H h) y := by
      intro y
      rw [hrep]
      exact transportWeight_rep_mul W h y
    -- the supports lie in the translated window
    have hSg : ∀ x, transportWeight W g x ≠ 0 →
        x ∈ T'.image fun y : H ↦ rep H g * (y : G) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := transportWeight_ne_zero W g x hx
      exact Finset.mem_image_of_mem _ (hT'g y hy)
    have hSh : ∀ x, transportWeight W h x ≠ 0 →
        x ∈ T'.image fun y : H ↦ rep H g * (y : G) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := transportWeight_ne_zero W h x hx
      rw [← hrep]
      exact Finset.mem_image_of_mem _ (hT'h y hy)
    -- both windows compute the same sum, because each omits only zeros
    have hzero : ∀ x : G, x ∉ T'.image (fun y : H ↦ rep H g * (y : G)) →
        |transportWeight W g x - transportWeight W h x| = 0 := by
      intro x hx
      have h1 : transportWeight W g x = 0 := by
        by_contra hc
        exact hx (hSg x hc)
      have h2 : transportWeight W h x = 0 := by
        by_contra hc
        exact hx (hSh x hc)
      rw [h1, h2, sub_self, abs_zero]
    have hzeroT : ∀ x : G, x ∉ T →
        |transportWeight W g x - transportWeight W h x| = 0 := by
      intro x hx
      have h1 : transportWeight W g x = 0 := by
        by_contra hc
        exact hx (hTg x hc)
      have h2 : transportWeight W h x = 0 := by
        by_contra hc
        exact hx (hTh x hc)
      rw [h1, h2, sub_self, abs_zero]
    have hTsum : ∑ x ∈ T ∩ T'.image (fun y : H ↦ rep H g * (y : G)),
          |transportWeight W g x - transportWeight W h x|
        = ∑ x ∈ T, |transportWeight W g x - transportWeight W h x| :=
      Finset.sum_subset Finset.inter_subset_left fun x hxT hx ↦
        hzero x fun hmem ↦ hx (Finset.mem_inter.mpr ⟨hxT, hmem⟩)
    have hSsum : ∑ x ∈ T ∩ T'.image (fun y : H ↦ rep H g * (y : G)),
          |transportWeight W g x - transportWeight W h x|
        = ∑ x ∈ T'.image (fun y : H ↦ rep H g * (y : G)),
            |transportWeight W g x - transportWeight W h x| :=
      Finset.sum_subset Finset.inter_subset_right fun x hx hx' ↦
        hzeroT x fun hmem ↦ hx' (Finset.mem_inter.mpr ⟨hmem, hx⟩)
    rw [← hTsum, hSsum]
    rw [Finset.sum_image fun a _ b _ hab ↦ Subtype.ext (mul_left_cancel hab)]
    calc ∑ y ∈ T', |transportWeight W g (rep H g * (y : G))
            - transportWeight W h (rep H g * (y : G))|
        = ∑ y ∈ T', |W.weight (part H g) y - W.weight (part H h) y| := by
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          rw [hgval y, hhval y]
      _ ≤ ε := hclose

/-! ## The printed lemma -/

/-- A finite set is covered by one member of a directed family of subgroups
whose union is everything. -/
theorem exists_mem_of_directed {ι : Type*} [Nonempty ι] {K : ι → Subgroup G}
    (hdir : Directed (· ≤ ·) K) (hcov : ∀ g : G, ∃ i, g ∈ K i) (R : Finset G) :
    ∃ i, ∀ g ∈ R, g ∈ K i := by
  classical
  refine Finset.induction_on R ?_ ?_
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i, by simp⟩
  · rintro a s _ha ⟨i, hi⟩
    obtain ⟨j, hj⟩ := hcov a
    obtain ⟨k, hik, hjk⟩ := hdir i j
    refine ⟨k, fun g hg ↦ ?_⟩
    rcases Finset.mem_insert.mp hg with rfl | hg'
    · exact hjk hj
    · exact hik (hi g hg')

/-- **The printed increasing-union lemma, in the discrete case.**  A group that
is the union of a directed family of subgroups each of which has property A has
property A itself.

This is `\cite[Lemma 2.5]{KWExact}` as the manuscript uses it: no openness
hypothesis appears, because in a discrete group every subgroup is open. -/
theorem hasPropertyA_of_directed {ι : Type*} [Nonempty ι] {K : ι → Subgroup G}
    (hdir : Directed (· ≤ ·) K) (hcov : ∀ g : G, ∃ i, g ∈ K i)
    (hA : ∀ i, HasPropertyA (K i)) : HasPropertyA G := by
  intro R ε hε
  obtain ⟨i, hi⟩ := exists_mem_of_directed hdir hcov R
  exact nonempty_propertyAWitness_of_subgroup (hA i) R hi hε

/-- The same for an increasing chain, which is the shape both the printed `Q_n`
and the repository's mapping telescopes have. -/
theorem hasPropertyA_of_monotone {K : ℕ → Subgroup G} (hmono : Monotone K)
    (hcov : ∀ g : G, ∃ n, g ∈ K n) (hA : ∀ n, HasPropertyA (K n)) :
    HasPropertyA G :=
  hasPropertyA_of_directed (K := K)
    (fun m n ↦ ⟨max m n, hmono (le_max_left m n), hmono (le_max_right m n)⟩)
    hcov hA

/-- **Property A is a local property.**  A group has property A as soon as the
subgroup generated by each finite set does. -/
theorem hasPropertyA_of_forall_closure
    (h : ∀ R : Finset G, HasPropertyA (Subgroup.closure (R : Set G))) :
    HasPropertyA G := by
  intro R ε hε
  exact nonempty_propertyAWitness_of_subgroup (h R) R
    (fun g hg ↦ Subgroup.subset_closure (Finset.mem_coe.mpr hg)) hε

/-- Property A is detected by the finitely generated subgroups. -/
theorem hasPropertyA_of_forall_fg
    (h : ∀ H : Subgroup G, H.FG → HasPropertyA H) : HasPropertyA G :=
  hasPropertyA_of_forall_closure fun R ↦ h _ ⟨R, rfl⟩

end PropertyALocality
end GroupApproximation
