import GroupApproximation.Dynamics.PartialShiftClasses
import GroupApproximation.Dynamics.ReturnPlacement
import GroupApproximation.Meta.AxiomGuard

/-!
# Saturated partial-shift classes and their levels

`non_mf_groups_exist.tex`, `\label{lem:transient-matrices}`, proof, tex 1489–1511:

> A compact subset $C\subset U$ has a finite cover by wandering clopen sets, say $m$ of them, so
> each orbit meets $C$ in at most $m$ points.  [...]  The equivalence relation they generate on
> $C$ has classes of size at most $m$.  Erasing loops shortens any path between related points to
> at most $m-1$ steps.  [...]  On each cell the classes have a fixed size $h$ and continuously
> enumerated clopen levels.

This module works over theoremc-retire's `Dynamics/PartialShiftClasses` (`reachableExponents`,
`ExponentBound`, `baseSet`, `baseCell`, `level`) and proves what the tower construction consumes.

* `exponentBound_of_wanderingCover`: a cover of `C` by `m` wandering sets gives the orbit bound,
  that each orbit meets `C` in at most `m` points.
* `reachableExponents_eq_of_le`: erasing loops.  The exponents reached in `m - 1` steps are the
  exponents reached in any larger number of steps.
* `add_mem_reachableExponents`, `neg_mem_reachableExponents`: concatenating and reversing paths.
* `reachableExponents_zpow_eq`: seen from another of its points, a class is the same class,
  translated.
* `exists_mem_baseCell_level`: every point of `C` is a level point over the representative of its
  class.
* `eq_of_zpow_eq_of_mem_baseSet`, `disjoint_level`: representatives and levels are unique.

The representative here is the point of least exponent in its class (`baseSet`), not "the point in
the first occupied atom".  Both give a clopen set of representatives, and the least exponent is the
choice `PartialShiftClasses` encodes.
-/

namespace GroupApproximation.ChainCore

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} {C : Set X} {E : Finset ℤ} {m : ℕ}

/-! ### The orbit bound from a wandering cover -/

/-- **Each orbit meets `C` in at most `m` points** (tex 1489–1491), when `C` is covered by `m`
wandering sets. -/
theorem exponentBound_of_wanderingCover {W : Fin m → Set X}
    (hWw : ∀ i, Dynamics.IsWandering T.toEquiv (W i)) (hCW : C ⊆ ⋃ i, W i) :
    ExponentBound T C m := by
  intro x S hS
  have hsel : ∀ n ∈ S, ∃ i : ℕ, ∃ hi : i < m, (T ^ n) x ∈ W ⟨i, hi⟩ := fun n hn => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hCW (hS n hn))
    exact ⟨i, i.2, hi⟩
  choose! ι hι using hsel
  have hinj : Set.InjOn ι (S : Set ℤ) := by
    intro n hn n' hn' heq
    obtain ⟨hlt, h1⟩ := hι n hn
    obtain ⟨hlt', h2⟩ := hι n' hn'
    have hfin : (⟨ι n, hlt⟩ : Fin m) = ⟨ι n', hlt'⟩ := Fin.ext heq
    rw [hfin] at h1
    have hmem : (T ^ (n - n')) ((T ^ n') x) ∈ W ⟨ι n', hlt'⟩ := by
      rwa [Dynamics.zpow_apply_zpow_apply, sub_add_cancel]
    have hd := Dynamics.eq_zero_of_isWandering T (hWw _) h2 hmem
    omega
  calc S.card ≤ (Finset.range m).card :=
        Finset.card_le_card_of_injOn ι
          (fun n hn => Finset.mem_coe.2 (Finset.mem_range.2 (hι n hn).1)) hinj
    _ = m := Finset.card_range m

/-! ### Erasing loops: saturation after `m - 1` steps -/

open Classical in
/-- The next stage of `reachableExponents` is a function of the current stage. -/
theorem reachableExponents_succ_eq (r : ℕ) (x : X) :
    reachableExponents T C E (r + 1) x =
      (reachableExponents T C E r x ∪
        ((reachableExponents T C E r x).biUnion fun a => (stepExponents E).image (a + ·))).filter
          fun d => (T ^ d) x ∈ C :=
  rfl

theorem reachableExponents_succ_succ_eq {r : ℕ} {x : X}
    (h : reachableExponents T C E (r + 1) x = reachableExponents T C E r x) :
    reachableExponents T C E (r + 1 + 1) x = reachableExponents T C E (r + 1) x := by
  rw [reachableExponents_succ_eq (r + 1), h, ← reachableExponents_succ_eq r]
  exact h

/-- Once two consecutive stages agree, every later stage has the same value. -/
theorem reachableExponents_eq_of_succ_eq {s : ℕ} {x : X}
    (h : reachableExponents T C E (s + 1) x = reachableExponents T C E s x) (t : ℕ) (hst : s ≤ t) :
    reachableExponents T C E t x = reachableExponents T C E s x := by
  have step : ∀ u : ℕ, s ≤ u →
      reachableExponents T C E (u + 1) x = reachableExponents T C E u x := by
    intro u hsu
    induction u, hsu using Nat.le_induction with
    | base => exact h
    | succ u _ ih => exact reachableExponents_succ_succ_eq ih
  induction t, hst using Nat.le_induction with
  | base => rfl
  | succ t hst ih => rw [step t hst, ih]

/-- Some stage among the first `m` agrees with the next one: the stages grow strictly until they
stop, and a class has at most `m` exponents. -/
theorem exists_reachableExponents_succ_eq (hm : ExponentBound T C m) (x : X) :
    ∃ s : ℕ, s ≤ m - 1 ∧
      reachableExponents T C E (s + 1) x = reachableExponents T C E s x := by
  by_cases hx : x ∈ C
  · by_contra hne
    push Not at hne
    have hgrow : ∀ s : ℕ, s ≤ m → s + 1 ≤ (reachableExponents T C E s x).card := by
      intro s hs
      induction s with
      | zero => exact Finset.card_pos.2 ⟨0, zero_mem_reachableExponents hx⟩
      | succ s ih =>
        have hlt : (reachableExponents T C E s x).card <
            (reachableExponents T C E (s + 1) x).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
            ⟨reachableExponents_subset_succ s x, (hne s (by omega)).symm⟩)
        have := ih (by omega)
        omega
    have h1 := hgrow m le_rfl
    have h2 := card_reachableExponents_le (E := E) hm m x
    omega
  · refine ⟨0, Nat.zero_le _, ?_⟩
    have h0 : ∀ d, d ∉ reachableExponents T C E 0 x := fun d hd =>
      hx (mem_reachableExponents_zero.1 hd).2
    ext d
    constructor
    · intro hd
      rcases (mem_reachableExponents_succ.1 hd).1 with hd0 | ⟨a, ha, -⟩
      · exact hd0
      · exact (h0 a ha).elim
    · intro hd
      exact (h0 d hd).elim

/-- **Erasing loops** (tex 1496–1497): the exponents reached in `m - 1` steps are all the
exponents reached in any larger number of steps. -/
theorem reachableExponents_eq_of_le (hm : ExponentBound T C m) (x : X) {r : ℕ} (hr : m - 1 ≤ r) :
    reachableExponents T C E r x = reachableExponents T C E (m - 1) x := by
  obtain ⟨s, hs, heq⟩ := exists_reachableExponents_succ_eq (E := E) hm x
  rw [reachableExponents_eq_of_succ_eq heq r (by omega),
    reachableExponents_eq_of_succ_eq heq (m - 1) hs]

/-! ### Concatenating and reversing paths -/

/-- A path of `r` steps from `T^a x`, after a path of `s` steps from `x` to `T^a x`. -/
theorem add_mem_reachableExponents {s : ℕ} {x : X} {a : ℤ}
    (ha : a ∈ reachableExponents T C E s x) :
    ∀ (r : ℕ) {d : ℤ}, d ∈ reachableExponents T C E r ((T ^ a) x) →
      d + a ∈ reachableExponents T C E (r + s) x := by
  intro r
  induction r with
  | zero =>
    intro d hd
    obtain ⟨rfl, -⟩ := mem_reachableExponents_zero.1 hd
    simpa only [zero_add] using ha
  | succ r ih =>
    intro d hd
    obtain ⟨hcase, hdC⟩ := mem_reachableExponents_succ.1 hd
    have hidx : r + 1 + s = r + s + 1 := by omega
    rw [hidx]
    refine mem_reachableExponents_succ.2 ⟨?_, ?_⟩
    · rcases hcase with hd' | ⟨b, hb, e, he, rfl⟩
      · exact Or.inl (ih hd')
      · exact Or.inr ⟨b + a, ih hb, e, he, by ring⟩
    · rwa [← Dynamics.zpow_apply_zpow_apply]

/-- Reversing a path: from `T^a x` the exponent `-a` returns to `x` in as many steps. -/
theorem neg_mem_reachableExponents {x : X} :
    ∀ (s : ℕ) {a : ℤ}, a ∈ reachableExponents T C E s x →
      -a ∈ reachableExponents T C E s ((T ^ a) x) := by
  intro s
  induction s with
  | zero =>
    intro a ha
    obtain ⟨rfl, hx⟩ := mem_reachableExponents_zero.1 ha
    refine mem_reachableExponents_zero.2 ⟨neg_zero, ?_⟩
    rwa [zpow_zero, Homeomorph.one_apply]
  | succ s ih =>
    intro a ha
    obtain ⟨hcase, haC⟩ := mem_reachableExponents_succ.1 ha
    rcases hcase with ha' | ⟨b, hb, e, he, rfl⟩
    · exact reachableExponents_subset_succ s _ (ih ha')
    · have hstep : -e ∈ reachableExponents T C E 1 ((T ^ (b + e)) x) := by
        refine mem_reachableExponents_succ.2 ⟨Or.inr ⟨0, zero_mem_reachableExponents haC, -e,
          neg_mem_stepExponents he, zero_add _⟩, ?_⟩
        rw [Dynamics.zpow_apply_zpow_apply, show -e + (b + e) = b by ring]
        exact zpow_mem_of_mem_reachableExponents hb
      have hback : -b ∈ reachableExponents T C E s ((T ^ (-e)) ((T ^ (b + e)) x)) := by
        rw [Dynamics.zpow_apply_zpow_apply, show -e + (b + e) = b by ring]
        exact ih hb
      have key := add_mem_reachableExponents hstep s hback
      rw [show -b + -e = -(b + e) by ring] at key
      exact key

/-! ### Translating a class -/

/-- **A class seen from one of its points** is the same class, translated. -/
theorem reachableExponents_zpow_eq (hm : ExponentBound T C m) {x : X} {a : ℤ}
    (ha : a ∈ reachableExponents T C E (m - 1) x) :
    reachableExponents T C E (m - 1) ((T ^ a) x) =
      (reachableExponents T C E (m - 1) x).image (· - a) := by
  ext d
  rw [Finset.mem_image]
  constructor
  · intro hd
    have h := add_mem_reachableExponents ha (m - 1) hd
    rw [reachableExponents_eq_of_le hm x (r := m - 1 + (m - 1)) (by omega)] at h
    exact ⟨d + a, h, add_sub_cancel_right d a⟩
  · rintro ⟨c, hc, rfl⟩
    have hneg := neg_mem_reachableExponents (m - 1) ha
    have hc' : c ∈ reachableExponents T C E (m - 1) ((T ^ (-a)) ((T ^ a) x)) := by
      rw [Dynamics.zpow_apply_zpow_apply, neg_add_cancel, zpow_zero, Homeomorph.one_apply]
      exact hc
    have h := add_mem_reachableExponents hneg (m - 1) hc'
    rw [reachableExponents_eq_of_le hm ((T ^ a) x) (r := m - 1 + (m - 1)) (by omega),
      ← sub_eq_add_neg] at h
    exact h

/-! ### Representatives and levels -/

/-- **Every point of `C` is a level point** over the representative of its class: the point of
least exponent. -/
theorem exists_mem_baseCell_level (hm : ExponentBound T C m) {z : X} (hz : z ∈ C) :
    ∃ (x : X) (d : ℤ), x ∈ baseCell T C E m (reachableExponents T C E (m - 1) x) ∧
      d ∈ reachableExponents T C E (m - 1) x ∧ (T ^ d) x = z := by
  obtain ⟨d0, hd0mem, hmin⟩ : ∃ d0 ∈ reachableExponents T C E (m - 1) z,
      ∀ c ∈ reachableExponents T C E (m - 1) z, d0 ≤ c :=
    ⟨_, Finset.min'_mem _ ⟨0, zero_mem_reachableExponents hz⟩,
      fun c hc => Finset.min'_le _ c hc⟩
  have htrans := reachableExponents_zpow_eq hm hd0mem
  refine ⟨(T ^ d0) z, -d0, ⟨⟨zpow_mem_of_mem_reachableExponents hd0mem, ?_⟩, rfl⟩, ?_, ?_⟩
  · intro d hd
    rw [htrans, Finset.mem_image] at hd
    obtain ⟨c, hc, rfl⟩ := hd
    have := hmin c hc
    omega
  · rw [htrans, Finset.mem_image]
    exact ⟨0, zero_mem_reachableExponents hz, zero_sub d0⟩
  · rw [Dynamics.zpow_apply_zpow_apply, neg_add_cancel, zpow_zero, Homeomorph.one_apply]

/-- **Representatives are unique** (tex 1505–1507): a point reached from two representatives by
exponents of their classes determines the representative and the exponent. -/
theorem eq_of_zpow_eq_of_mem_baseSet (hm : ExponentBound T C m) {x x' : X} {d d' : ℤ}
    (hx : x ∈ baseSet T C E m) (hx' : x' ∈ baseSet T C E m)
    (hd : d ∈ reachableExponents T C E (m - 1) x)
    (hd' : d' ∈ reachableExponents T C E (m - 1) x')
    (h : (T ^ d) x = (T ^ d') x') : x = x' ∧ d = d' := by
  have hz := reachableExponents_zpow_eq hm hd
  have hneg : -d' ∈ reachableExponents T C E (m - 1) ((T ^ d) x) := by
    rw [h]
    exact neg_mem_reachableExponents (m - 1) hd'
  rw [hz, Finset.mem_image] at hneg
  obtain ⟨c, hc, hcd⟩ := hneg
  have hx'eq : (T ^ c) x = x' := by
    have hc' : c = d - d' := by omega
    rw [hc']
    exact Dynamics.zpow_sub_apply_of_eq T h.symm
  have hx'R := reachableExponents_zpow_eq hm hc
  rw [hx'eq] at hx'R
  have h0 : (0 : ℤ) - c ∈ reachableExponents T C E (m - 1) x' := by
    rw [hx'R, Finset.mem_image]
    exact ⟨0, zero_mem_reachableExponents hx.1, rfl⟩
  have hc0 : 0 ≤ c := hx.2 c hc
  have hc0' : 0 ≤ 0 - c := hx'.2 _ h0
  have hc00 : c = 0 := by omega
  refine ⟨?_, by omega⟩
  rw [← hx'eq, hc00, zpow_zero, Homeomorph.one_apply]

/-- **Distinct levels are disjoint**: the level of exponent `d ∈ S` over the cell `S` meets the
level of `d' ∈ S'` over `S'` only when `(S, d) = (S', d')`. -/
theorem disjoint_level (hm : ExponentBound T C m) {S S' : Finset ℤ} {d d' : ℤ}
    (hd : d ∈ S) (hd' : d' ∈ S') (hne : (S, d) ≠ (S', d')) :
    Disjoint (level T C E m S d) (level T C E m S' d') := by
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨x, hx, rfl⟩ := mem_level_iff.1 hz
  obtain ⟨x', hx', hxx'⟩ := mem_level_iff.1 hz'
  have hxS : reachableExponents T C E (m - 1) x = S := hx.2
  have hxS' : reachableExponents T C E (m - 1) x' = S' := hx'.2
  have hdx : d ∈ reachableExponents T C E (m - 1) x := by rw [hxS]; exact hd
  have hdx' : d' ∈ reachableExponents T C E (m - 1) x' := by rw [hxS']; exact hd'
  obtain ⟨hxeq, hdeq⟩ := eq_of_zpow_eq_of_mem_baseSet hm hx.1 hx'.1 hdx hdx' hxx'.symm
  apply hne
  rw [← hxS, ← hxS', hxeq, hdeq]

/-- The levels over a cell lie in `C`. -/
theorem level_subset {S : Finset ℤ} {d : ℤ} (hd : d ∈ S) : level T C E m S d ⊆ C := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := mem_level_iff.1 hz
  have hxS : reachableExponents T C E (m - 1) x = S := hx.2
  rw [← hxS] at hd
  exact zpow_mem_of_mem_reachableExponents hd

end GroupApproximation.ChainCore

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.ChainCore.exponentBound_of_wanderingCover
#audit_axioms GroupApproximation.ChainCore.reachableExponents_eq_of_le
#audit_axioms GroupApproximation.ChainCore.neg_mem_reachableExponents
#audit_axioms GroupApproximation.ChainCore.reachableExponents_zpow_eq
#audit_axioms GroupApproximation.ChainCore.exists_mem_baseCell_level
#audit_axioms GroupApproximation.ChainCore.eq_of_zpow_eq_of_mem_baseSet
#audit_axioms GroupApproximation.ChainCore.disjoint_level
#audit_axioms GroupApproximation.ChainCore.level_subset
