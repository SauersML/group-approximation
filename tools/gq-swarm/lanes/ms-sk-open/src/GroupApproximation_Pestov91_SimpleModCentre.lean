import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.NonUnitalSubring.Basic
import GroupApproximation.Leavitt.ElementarySimplicity
import GroupApproximation.Pestov91.Centre

/-!
# `EL_ι(R)/Z(EL_ι(R))` is simple over a simple ring with local annihilation

Let `R` be a ring and `ι` a finite index type with at least three elements.  This module
proves that `EL_ι(R)/Z(EL_ι(R))` is a simple group as soon as

* `R` is a simple ring (`IsSimpleRing R`), and
* `R` has **local annihilation** (`LocalAnnihilation R`): for every finite `F ⊆ R`, the
  elements `s` admitting some `t ≠ 0` with `t * s = 0` and `t * f * s = 0` for all `f ∈ F`
  generate `R` as a non-unital ring.

No sandwich theorem for normal subgroups and no stable-range hypothesis is used.

## Route

1. Let `N` be a normal subgroup that is not central, and pick `g ∈ N` outside the centre.
   The coefficients `s` whose roots commute with `g` form a non-unital subring.  So local
   annihilation, applied to the entries of `g`, gives `s`, `t ≠ 0` and a root
   `h = e_{ij}(s)` that does not commute with `g`, with `t * s = 0` and `t * g_{pk} * s = 0`.
2. `ρ = g h g⁻¹ h⁻¹` lies in `N`, is not `1`, and satisfies `t • (ρ - 1) = 0`.
3. Simplicity of `R` gives `c` with `(ρ - 1)_{qm} * c * t ≠ 0`.  The commutator of `ρ` with
   `e_{ml}(c * t)` is the one-column matrix `1 + (ρ - 1) e_{ml}(c * t)`, and
   `ElementarySimplicity.exists_elGen_mem_of_colMatrix_mem` extracts a nonzero root in `N`.
4. The coefficients `a` with `e_{pq}(a) ∈ N` for all `p ≠ q` form a two-sided ideal.  It is
   nonzero, so it contains `1`, so `N = ⊤`.

This departs from the tower / `SL_d(𝔽_q)` argument of the Pestov 9.1 write-up: the ring
enters only through `IsSimpleRing` and `LocalAnnihilation`.
-/

namespace GroupApproximation
namespace Pestov91

open ElementarySimplicity

/-- **Local annihilation.**  For every finite `F ⊆ R`, the elements `s` killed on the left by
some `t ≠ 0`, together with every `f * s` for `f ∈ F`, generate `R` as a non-unital ring. -/
def LocalAnnihilation (R : Type*) [Ring R] : Prop :=
  ∀ F : Finset R, NonUnitalSubring.closure
    {s : R | ∃ t : R, t ≠ 0 ∧ t * s = 0 ∧ ∀ f ∈ F, t * f * s = 0} = ⊤

namespace SimpleModCentre

section Group

variable {G : Type*} [Group G]

/-- A commutator with a left entry in a normal subgroup lies in it. -/
theorem normal_comm_mem_left (N : Subgroup G) [hN : N.Normal] {x : G} (hx : x ∈ N) (g : G) :
    x * g * x⁻¹ * g⁻¹ ∈ N := by
  have h := N.mul_mem hx (hN.conj_mem x⁻¹ (N.inv_mem hx) g)
  simpa only [mul_assoc] using h

/-- A commutator with a right entry in a normal subgroup lies in it. -/
theorem normal_comm_mem_right (N : Subgroup G) [hN : N.Normal] {x : G} (hx : x ∈ N) (g : G) :
    g * x * g⁻¹ * x⁻¹ ∈ N :=
  N.mul_mem (hN.conj_mem x hx g) (N.inv_mem hx)

end Group

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

theorem elGen_inv' (i j : ι) (h : i ≠ j) (a : R) : (elGen i j h a)⁻¹ = elGen i j h (-a) :=
  inv_eq_of_mul_eq_one_right (by rw [elGen_mul, add_neg_cancel, elGen_zero])

/-- A root in a normal subgroup keeps its coefficient when its target index moves. -/
theorem elGen_mem_target (N : Subgroup (elementaryGroup ι R)) [N.Normal] {i j : ι}
    (hij : i ≠ j) {a : R} (hmem : elGen i j hij a ∈ N) {k : ι} (hik : i ≠ k) :
    elGen i k hik a ∈ N := by
  by_cases hjk : j = k
  · subst hjk; exact hmem
  · have h := normal_comm_mem_left N hmem (elGen j k hjk 1)
    rwa [elGen_commutator i j k hij hjk hik, mul_one] at h

/-- A root in a normal subgroup keeps its coefficient when its source index moves. -/
theorem elGen_mem_source (N : Subgroup (elementaryGroup ι R)) [N.Normal] {i j : ι}
    (hij : i ≠ j) {a : R} (hmem : elGen i j hij a ∈ N) {k : ι} (hkj : k ≠ j) :
    elGen k j hkj a ∈ N := by
  by_cases hki : k = i
  · subst hki; exact hmem
  · have h := normal_comm_mem_right N hmem (elGen k i hki 1)
    rwa [elGen_commutator k i j hki hij hkj, one_mul] at h

/-- A root in a normal subgroup puts its coefficient at every position. -/
theorem elGen_mem_all (hcard : 3 ≤ Fintype.card ι) (N : Subgroup (elementaryGroup ι R))
    [N.Normal] {i j : ι} (hij : i ≠ j) {a : R} (hmem : elGen i j hij a ∈ N) {p q : ι}
    (hpq : p ≠ q) : elGen p q hpq a ∈ N := by
  obtain ⟨k, hki, hkp⟩ := exists_third_index hcard i p
  exact elGen_mem_target N (Ne.symm hkp)
    (elGen_mem_source N (Ne.symm hki) (elGen_mem_target N hij hmem (Ne.symm hki))
      (Ne.symm hkp)) hpq

/-- The coefficients of the roots lying in a normal subgroup form a two-sided ideal. -/
def levelIdeal (hcard : 3 ≤ Fintype.card ι) (N : Subgroup (elementaryGroup ι R)) [N.Normal] :
    TwoSidedIdeal R :=
  TwoSidedIdeal.mk' {a | ∀ (p q : ι) (hpq : p ≠ q), elGen p q hpq a ∈ N}
    (fun p q hpq => by rw [elGen_zero]; exact N.one_mem)
    (fun {a b} ha hb p q hpq => by
      rw [← elGen_mul]; exact N.mul_mem (ha p q hpq) (hb p q hpq))
    (fun {a} ha p q hpq => by rw [← elGen_inv']; exact N.inv_mem (ha p q hpq))
    (fun {x a} ha p q hpq => by
      obtain ⟨k, hkp, hkq⟩ := exists_third_index hcard p q
      rw [← elGen_commutator p k q (Ne.symm hkp) hkq hpq x a]
      exact normal_comm_mem_right N (ha k q hkq) _)
    (fun {a x} ha p q hpq => by
      obtain ⟨k, hkp, hkq⟩ := exists_third_index hcard p q
      rw [← elGen_commutator p k q (Ne.symm hkp) hkq hpq a x]
      exact normal_comm_mem_left N (ha p k (Ne.symm hkp)) _)

theorem mem_levelIdeal (hcard : 3 ≤ Fintype.card ι) (N : Subgroup (elementaryGroup ι R))
    [N.Normal] (a : R) :
    a ∈ levelIdeal hcard N ↔ ∀ (p q : ι) (hpq : p ≠ q), elGen p q hpq a ∈ N :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ a

/-- **Level ideal.**  Over a simple ring, a normal subgroup containing one nonzero root is the
whole elementary group. -/
theorem normal_eq_top_of_elGen_mem (hcard : 3 ≤ Fintype.card ι) [IsSimpleRing R]
    (N : Subgroup (elementaryGroup ι R)) [N.Normal] {i j : ι} (hij : i ≠ j) {x : R}
    (hx : x ≠ 0) (hmem : elGen i j hij x ∈ N) : N = ⊤ := by
  have h1 : (1 : R) ∈ levelIdeal hcard N :=
    IsSimpleRing.one_mem_of_ne_zero_mem _ hx
      ((mem_levelIdeal hcard N x).mpr fun p q hpq => elGen_mem_all hcard N hij hmem hpq)
  rw [Subgroup.eq_top_iff']
  intro g
  have hg := elementaryGroup_hom_eq_one_of_gens (QuotientGroup.mk' N)
    (fun l k hlk d => by
      have hd := TwoSidedIdeal.mul_mem_left _ d 1 h1
      rw [mul_one] at hd
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact (mem_levelIdeal hcard N d).mp hd l k hlk) g
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hg

/-- In a simple ring, two nonzero elements `a`, `t` admit `c` with `a * c * t ≠ 0`. -/
theorem exists_mul_mul_ne_zero [IsSimpleRing R] {a t : R} (ha : a ≠ 0) (ht : t ≠ 0) :
    ∃ c : R, a * c * t ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hJ : ∃ J : TwoSidedIdeal R, ∀ x : R, x ∈ J ↔ ∀ c : R, x * c * t = 0 :=
    ⟨TwoSidedIdeal.mk' {x | ∀ c : R, x * c * t = 0}
      (fun c => by simp)
      (fun {x y} hx hy c => by rw [add_mul, add_mul, hx c, hy c, add_zero])
      (fun {x} hx c => by rw [neg_mul, neg_mul, hx c, neg_zero])
      (fun {x y} hy c => by rw [mul_assoc x y c, mul_assoc x (y * c) t, hy c, mul_zero])
      (fun {x y} hx c => by rw [mul_assoc x y c]; exact hx (y * c)),
      fun x => TwoSidedIdeal.mem_mk' _ _ _ _ _ _ x⟩
  obtain ⟨J, hJ⟩ := hJ
  have h1 : (1 : R) ∈ J := IsSimpleRing.one_mem_of_ne_zero_mem J ha ((hJ a).mpr hcon)
  have ht0 := (hJ 1).mp h1 1
  rw [one_mul, one_mul] at ht0
  exact ht ht0

/-- The coefficients whose roots all commute with `g` form a non-unital subring. -/
def commutingSubring (hcard : 3 ≤ Fintype.card ι) (g : elementaryGroup ι R) :
    NonUnitalSubring R where
  carrier := {s | ∀ (i j : ι) (hij : i ≠ j), Commute g (elGen i j hij s)}
  zero_mem' := fun i j hij => by rw [elGen_zero]; exact Commute.one_right g
  add_mem' := fun {a b} ha hb i j hij => by
    rw [← elGen_mul]; exact (ha i j hij).mul_right (hb i j hij)
  neg_mem' := fun {a} ha i j hij => by rw [← elGen_inv']; exact (ha i j hij).inv_right
  mul_mem' := fun {a b} ha hb i j hij => by
    obtain ⟨k, hki, hkj⟩ := exists_third_index hcard i j
    rw [← elGen_commutator i k j (Ne.symm hki) hkj hij a b]
    exact (((ha i k (Ne.symm hki)).mul_right (hb k j hkj)).mul_right
      (ha i k (Ne.symm hki)).inv_right).mul_right (hb k j hkj).inv_right

/-- An element commuting with every root is central. -/
theorem mem_center_of_commute_elGen (g : elementaryGroup ι R)
    (hg : ∀ (i j : ι) (hij : i ≠ j) (s : R), Commute g (elGen i j hij s)) :
    g ∈ Subgroup.center (elementaryGroup ι R) := by
  rw [Subgroup.mem_center_iff]
  intro x
  suffices h : Commute x g from h.eq
  obtain ⟨x, hx⟩ := x
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨l, k, hlk, d, rfl⟩ := hy
      exact (hg l k hlk d).symm
  | one => exact Commute.one_left g
  | mul y z hy hz ihy ihz =>
      have h : (⟨y * z, Subgroup.mul_mem _ hy hz⟩ : elementaryGroup ι R)
          = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [h]
      exact ihy.mul_left ihz
  | inv y hy ihy =>
      have h : (⟨y⁻¹, Subgroup.inv_mem _ hy⟩ : elementaryGroup ι R) = (⟨y, hy⟩)⁻¹ := rfl
      rw [h]
      exact ihy.inv_left

/-- **Annihilated commutator.**  If `t * s = 0` and `t * g_{pk} * s = 0` for all `p, k`, then
`t` kills `⁅g, e_{ij}(s)⁆ - 1` on the left. -/
theorem smul_elMat_commutator_sub_one (g : elementaryGroup ι R) {i j : ι} (hij : i ≠ j)
    {s t : R} (hts : t * s = 0) (htF : ∀ p k : ι, t * elMat g p k * s = 0) :
    t • (elMat (g * elGen i j hij s * g⁻¹ * (elGen i j hij s)⁻¹) - 1) = 0 := by
  have hGE : t • (elMat g * Matrix.single i j s) = 0 := by
    ext p k
    rw [Matrix.smul_apply, mul_single_apply, Matrix.zero_apply, smul_eq_mul]
    by_cases hk : k = j
    · rw [if_pos hk, ← mul_assoc]; exact htF p i
    · rw [if_neg hk, mul_zero]
  have hE : t • Matrix.single i j s = 0 := by
    rw [Matrix.smul_single, smul_eq_mul, hts, Matrix.single_zero]
  have hexp : elMat (g * elGen i j hij s * g⁻¹ * (elGen i j hij s)⁻¹) - 1 =
      elMat g * Matrix.single i j s * (elMat g⁻¹ * (1 - Matrix.single i j s))
        - Matrix.single i j s := by
    simp only [elMat_mul, elMat_elGen, elMat_elGen_inv]
    have hgg := elMat_mul_inv g
    calc elMat g * (1 + Matrix.single i j s) * elMat g⁻¹ * (1 - Matrix.single i j s) - 1
        = elMat g * elMat g⁻¹ * (1 - Matrix.single i j s)
            + elMat g * Matrix.single i j s * (elMat g⁻¹ * (1 - Matrix.single i j s)) - 1 := by
          noncomm_ring
      _ = elMat g * Matrix.single i j s * (elMat g⁻¹ * (1 - Matrix.single i j s))
            - Matrix.single i j s := by
          rw [hgg]; noncomm_ring
  rw [hexp, smul_sub,
    ← Matrix.smul_mul t (elMat g * Matrix.single i j s) (elMat g⁻¹ * (1 - Matrix.single i j s)),
    hGE, Matrix.zero_mul, hE, sub_zero]

/-- **Second commutator.**  If `t • (ρ - 1) = 0`, the commutator of `ρ` with `e_{ml}(c * t)` is
the one-column matrix `1 + (ρ - 1) e_{ml}(c * t)`. -/
theorem elMat_commutator_elGen_eq_colMatrix (ρ : elementaryGroup ι R) {m l : ι} (hml : m ≠ l)
    {c t : R} (hP : t • (elMat ρ - 1) = 0) :
    elMat (ρ * elGen m l hml (c * t) * ρ⁻¹ * (elGen m l hml (c * t))⁻¹) =
      1 + colMatrix l (fun x => (elMat ρ - 1) x m * (c * t)) := by
  have hSP : Matrix.single m l (c * t) * (elMat ρ - 1) = 0 := by
    ext r k
    rw [single_mul_apply, Matrix.zero_apply]
    by_cases hr : r = m
    · have h := congrFun (congrFun hP l) k
      rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h
      rw [if_pos hr, mul_assoc, h, mul_zero]
    · rw [if_neg hr]
  have hSA : Matrix.single m l (c * t) * elMat ρ = Matrix.single m l (c * t) := by
    rw [mul_sub, mul_one, sub_eq_zero] at hSP; exact hSP
  have hSA' : Matrix.single m l (c * t) * elMat ρ⁻¹ = Matrix.single m l (c * t) := by
    calc Matrix.single m l (c * t) * elMat ρ⁻¹
        = Matrix.single m l (c * t) * elMat ρ * elMat ρ⁻¹ := by rw [hSA]
      _ = Matrix.single m l (c * t) := by rw [mul_assoc, elMat_mul_inv, mul_one]
  have hSS := single_mul_self_eq_zero m l hml (c * t)
  have hAA' := elMat_mul_inv ρ
  rw [← mul_single_eq (elMat ρ - 1) m l (c * t)]
  simp only [elMat_mul, elMat_elGen, elMat_elGen_inv]
  calc elMat ρ * (1 + Matrix.single m l (c * t)) * elMat ρ⁻¹ * (1 - Matrix.single m l (c * t))
      = elMat ρ * elMat ρ⁻¹ * (1 - Matrix.single m l (c * t))
          + elMat ρ * (Matrix.single m l (c * t) * elMat ρ⁻¹)
            * (1 - Matrix.single m l (c * t)) := by
        noncomm_ring
    _ = 1 - Matrix.single m l (c * t) + elMat ρ * Matrix.single m l (c * t)
          - elMat ρ * (Matrix.single m l (c * t) * Matrix.single m l (c * t)) := by
        rw [hAA', hSA']; noncomm_ring
    _ = 1 + (elMat ρ - 1) * Matrix.single m l (c * t) := by
        rw [hSS]; noncomm_ring

/-- A nontrivial element of a normal subgroup killed on the left by some `t ≠ 0` yields a
nonzero root in the subgroup, over a simple ring. -/
theorem exists_elGen_mem_of_annihilated (hcard : 3 ≤ Fintype.card ι) [IsSimpleRing R]
    (N : Subgroup (elementaryGroup ι R)) [N.Normal] {ρ : elementaryGroup ι R} (hρN : ρ ∈ N)
    (hρ1 : ρ ≠ 1) {t : R} (ht : t ≠ 0) (hP : t • (elMat ρ - 1) = 0) :
    ∃ (i j : ι) (hij : i ≠ j) (x : R), x ≠ 0 ∧ elGen i j hij x ∈ N := by
  obtain ⟨q, m, hqm⟩ : ∃ q m : ι, (elMat ρ - 1) q m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hρ1
    apply elMat_injective
    rw [elMat_one, ← sub_eq_zero]
    ext p k
    exact hcon p k
  obtain ⟨c, hc⟩ := exists_mul_mul_ne_zero hqm ht
  obtain ⟨l, hlq, hlm⟩ := exists_third_index hcard q m
  obtain ⟨i, hiq, hil⟩ := exists_third_index hcard q l
  have hκN := normal_comm_mem_left N hρN (elGen m l (Ne.symm hlm) (c * t))
  have hval := elMat_commutator_elGen_eq_colMatrix ρ (Ne.symm hlm) (c := c) hP
  obtain ⟨x, hxN, hx⟩ := exists_elGen_mem_of_colMatrix_mem N hκN hval hiq hil 1
  refine ⟨i, l, hil, x, hx ?_, hxN⟩
  simpa only [one_mul, mul_assoc] using hc

/-- **Non-central normal subgroups contain a nonzero root.** -/
theorem exists_elGen_mem_of_not_mem_center (hcard : 3 ≤ Fintype.card ι) [IsSimpleRing R]
    (hloc : LocalAnnihilation R) (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    {g : elementaryGroup ι R} (hgN : g ∈ N)
    (hgZ : g ∉ Subgroup.center (elementaryGroup ι R)) :
    ∃ (i j : ι) (hij : i ≠ j) (x : R), x ≠ 0 ∧ elGen i j hij x ∈ N := by
  classical
  have hnot : ¬ ∀ s : R, (∃ t : R, t ≠ 0 ∧ t * s = 0 ∧ ∀ p k : ι, t * elMat g p k * s = 0) →
      ∀ (i j : ι) (hij : i ≠ j), Commute g (elGen i j hij s) := by
    intro hall
    apply hgZ
    apply mem_center_of_commute_elGen
    have hle : ⊤ ≤ commutingSubring hcard g := by
      rw [← hloc (Finset.univ.image fun pk : ι × ι => elMat g pk.1 pk.2),
        NonUnitalSubring.closure_le]
      rintro s ⟨t, ht, hts, htF⟩
      exact hall s ⟨t, ht, hts, fun p k =>
        htF _ (Finset.mem_image.mpr ⟨(p, k), Finset.mem_univ _, rfl⟩)⟩
    intro i j hij s
    exact hle (NonUnitalSubring.mem_top s) i j hij
  push Not at hnot
  obtain ⟨s, ⟨t, ht, hts, htF⟩, i, j, hij, hcomm⟩ := hnot
  refine exists_elGen_mem_of_annihilated hcard N
    (normal_comm_mem_left N hgN (elGen i j hij s)) ?_ ht
    (smul_elMat_commutator_sub_one g hij hts htF)
  intro h1
  apply hcomm
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

/-- Every normal subgroup of `EL_ι(R)` is central or everything. -/
theorem normal_le_center_or_eq_top (hcard : 3 ≤ Fintype.card ι) [IsSimpleRing R]
    (hloc : LocalAnnihilation R) (K : Subgroup (elementaryGroup ι R)) [K.Normal] :
    K ≤ Subgroup.center (elementaryGroup ι R) ∨ K = ⊤ := by
  by_cases hle : K ≤ Subgroup.center (elementaryGroup ι R)
  · exact Or.inl hle
  · obtain ⟨g, hgK, hgZ⟩ := SetLike.not_le_iff_exists.mp hle
    obtain ⟨i, j, hij, x, hx, hxK⟩ := exists_elGen_mem_of_not_mem_center hcard hloc K hgK hgZ
    exact Or.inr (normal_eq_top_of_elGen_mem hcard K hij hx hxK)

end SimpleModCentre

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- **`EL_ι(R)/Z(EL_ι(R))` is simple** for `|ι| ≥ 3`, a simple ring `R` and local annihilation.
-/
theorem isSimpleGroup_elementaryGroup_quotient_center (hcard : 3 ≤ Fintype.card ι)
    [IsSimpleRing R] (hloc : LocalAnnihilation R) :
    IsSimpleGroup (↥(elementaryGroup ι R) ⧸ Subgroup.center ↥(elementaryGroup ι R)) where
  exists_pair_ne := by
    obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card ι by omega)
    exact (elementaryModCentre_nontrivial (R := R) i j hij).exists_pair_ne
  eq_bot_or_eq_top_of_normal := by
    intro M hM
    have hK : (M.comap (QuotientGroup.mk' (Subgroup.center (elementaryGroup ι R)))).Normal :=
      hM.comap _
    rcases SimpleModCentre.normal_le_center_or_eq_top hcard hloc
        (M.comap (QuotientGroup.mk' (Subgroup.center (elementaryGroup ι R)))) with hle | htop
    · left
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (elementaryGroup ι R)) x
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hle (Subgroup.mem_comap.mpr hx)
    · right
      rw [Subgroup.eq_top_iff']
      intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (elementaryGroup ι R)) x
      have hy : y ∈ M.comap (QuotientGroup.mk' (Subgroup.center (elementaryGroup ι R))) := by
        rw [htop]; exact Subgroup.mem_top y
      exact Subgroup.mem_comap.mp hy

/-- The rank-`n` form, `n ≥ 3`. -/
theorem isSimpleGroup_elementaryGroup_fin_quotient_center {n : ℕ} (hn : 3 ≤ n)
    [IsSimpleRing R] (hloc : LocalAnnihilation R) :
    IsSimpleGroup (↥(elementaryGroup (Fin n) R) ⧸ Subgroup.center ↥(elementaryGroup (Fin n) R)) :=
  isSimpleGroup_elementaryGroup_quotient_center (by simpa using hn) hloc

/-- **`EL_3(R)/Z(EL_3(R))` is simple** over a simple ring with local annihilation. -/
theorem isSimpleGroup_elementaryModCentre_fin_three [IsSimpleRing R]
    (hloc : LocalAnnihilation R) :
    IsSimpleGroup (↥(elementaryGroup (Fin 3) R) ⧸ Subgroup.center ↥(elementaryGroup (Fin 3) R)) :=
  isSimpleGroup_elementaryGroup_quotient_center (by simp) hloc

end Pestov91
end GroupApproximation
