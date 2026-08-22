import GroupApproximation.Higman.AgreeClosure
import GroupApproximation.Higman.GeneratedEnumeration
import GroupApproximation.Higman.GeneratedTransition
import GroupApproximation.Higman.GeneratedValue
import GroupApproximation.Higman.OperationClosureTheta
import GroupApproximation.Higman.FinalReduction

/-!
# Higman's Theorem 3: the position calculus, and the one step that is left

`Higman.HigmanTheoremThree` (`Higman/TheoremFour.lean`) asks for

    ∀ B : Set Seq.E, REset B → Seq.HigmanGenerated B ,

and it is one of the four inputs of `Higman.statement_of_four`.  Six modules
already attack it from below: `Higman/GeneratedBasic.lean` (the lattice bottom,
`∅` and `univ` and finite `⋃`/`⋂`), `Higman/GeneratedCoords.lean` and
`Higman/GeneratedPin.lean` and `Higman/GeneratedValue.lean` (the value calculus:
`{c·e₀}` and `{f | f 0 = c}` for every integer `c`),
`Higman/GeneratedTransition.lean` (the adjacent-block device
`ω₂ₖ A ∩ σᵏ(ω₂ₖ A)`), and `Higman/GeneratedEnumeration.lean` (Lemma 2.8, with
the hypothesis `B.Nonempty` that the printed statement omits).

This module supplies the layer between them and then names, exactly, what is
still owed.

## 1.  The position calculus

Everything proved before this file is *anchored at the origin*: `pinZero`,
`pinOne`, `atZero`.  That is not an accident of presentation: `Z` and `S` sit at
the origin, `ζ` frees the coordinate `0` and `π` frees the strictly positive
ones, so every condition available so far is stated there.  Position elsewhere
has to be manufactured, and it is manufactured here, and cheaply:

* `higmanGenerated_pinAt` --- `{f | f d = c}` is generated for **every** index
  `d` and value `c`.  Non-negative `d` is `σᵈ` of `pinZero`
  (`sigmaOp_iterate_pinZero`); negative `d` is that reflected by `ρ`
  (`rhoOp_pinAt`).
* `higmanGenerated_vanishBelow`, `higmanGenerated_vanishAbove` --- the two
  half-lines `{f | ∀ i < N, f i = 0}` and `{f | ∀ i > N, f i = 0}`.  The seed is
  `ζ(π Z) = vanishBelow 0`: `π` of `Z` pins everything at and below the origin
  to zero, and `ζ` gives the origin back.
* `higmanGenerated_singleton` and `higmanGenerated_of_finite` --- **every finite
  set of sequences is generated.**  A single sequence is cut out by the two
  half-lines that bound its support together with one pin at each index of the
  bounding window, a finite intersection; a finite set is a finite union of
  those.

The last item is the measure of where the difficulty actually sits.  Before it
one could suspect the obstruction was the arithmetic of individual sequences;
it is not.  The family already contains every finite set, and what Theorem 3
still asks for is exactly the passage from finite unions to unions indexed by a
total computable enumeration.

## 2.  What is left, and why it is stated the way it is

`Higman.EnumeratedRangeGenerated` below is that passage and nothing else:

    ∀ c : ℕ → List (ℤ × ℤ), Computable c →
      Seq.HigmanGenerated {g | ∃ r, seqOfList (c r) = g} .

`higmanTheoremThree_of_enumeratedRange` derives the full input from it.  The
derivation is Higman's own endgame, and it uses both halves of what the
enumeration module proves: the empty set is discharged by
`Seq.higmanGenerated_empty` --- which is *required*, since Lemma 2.8 is false
at `X = ∅` --- and every nonempty recursively enumerable set is the exact range
of a total computable enumeration by `exists_computable_enumeration`.

Between them the two halves cover every `B` with `REset B`, which is why the
passage costs nothing.  The converse --- that such a range is itself recursively
enumerable --- is the easy direction of Theorem 3 and is not used here.

## 3.  The entry point for the construction that closes it

The route the transition device is built for runs a computation along the index
line: a set of *traces*, cut out block by block by that device, whose value
track is read off by compressing the blocks.  The compression is `θ` iterated,
because `θᵗ` reads the coordinates divisible by `2ᵗ`
(`mem_thetaOp_iterate_iff`), so a trace in blocks of width `2ᵗ` projects onto
its first track.  `higmanGenerated_of_transitionProjection` is that assembly in
one statement: a generated relation `A` between adjacent `k`-blocks, a
generated set `D` of anchoring conditions, and the identification of the
projection with the target.  Every ingredient of it is proved; what it still
needs supplied is the relation `A` and the anchors `D` --- the arithmetic of
bounded arity, which is the part of Higman's Section 2 that precedes his Lemma
2.8, and which `Higman/GeneratedTransition.lean` records as using the same
device again at his Lemmas 2.1, 2.4 and 2.5.

The pieces that construction will want are here too:
`higmanGenerated_pinAt` for the anchors, `higmanGenerated_vanishBelow` for the
half-line supports, and `higmanGenerated_agreeOp_nonneg` --- `ρ π ρ`, which
frees the negative coordinates and is the mirror of `π`, so that a condition can
be imposed on one half-line only.

## Reference

Higman 1961, Section 2 (Theorem 3), and Lemma 2.8 as corrected in
`Higman/GeneratedEnumeration.lean`.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

/-! ## 1.  Iterating the shift -/

/-- Iterated `σ` preserves generation.  This was inlined in
`higmanGenerated_transitionSet`; every construction below uses it. -/
theorem higmanGenerated_sigmaOp_iterate (n : ℕ) {B : Set E} (h : HigmanGenerated B) :
    HigmanGenerated (sigmaOp^[n] B) := by
  induction n with
  | zero => simpa using h
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact HigmanGenerated.sigma ih

/-! ## 2.  Pinning an arbitrary coordinate -/

/-- The sequences whose value at the index `d` is `c`, with every other
coordinate unconstrained. -/
def pinAt (d c : ℤ) : Set E := {f | f d = c}

theorem pinAt_zero (c : ℤ) : pinAt 0 c = pinZero c := rfl

/-- `σⁿ` moves a pin `n` steps to the right. -/
theorem sigmaOp_iterate_pinZero (n : ℕ) (c : ℤ) :
    sigmaOp^[n] (pinZero c) = pinAt (n : ℤ) c := by
  ext f
  rw [mem_sigmaOp_iterate_iff]
  constructor
  · rintro ⟨g, hg, h⟩
    have hg' : g 0 = c := hg
    show f (n : ℤ) = c
    rw [h (n : ℤ), sub_self, hg']
  · intro hf
    have hf' : f (n : ℤ) = c := hf
    obtain ⟨g, rfl⟩ := exists_shiftSeq_iterate n f
    refine ⟨g, ?_, fun i => shiftSeq_iterate_apply n g i⟩
    show g 0 = c
    have h0 := shiftSeq_iterate_apply n g (n : ℤ)
    rw [sub_self] at h0
    rw [← h0]
    exact hf'

/-- `ρ` reflects a pin. -/
theorem rhoOp_pinAt (d c : ℤ) : rhoOp (pinAt d c) = pinAt (-d) c := by
  ext f
  constructor
  · rintro ⟨g, hg, h⟩
    have hg' : g d = c := hg
    show f (-d) = c
    rw [h (-d), neg_neg, hg']
  · intro hf
    have hf' : f (-d) = c := hf
    refine ⟨reflect f, ?_, fun i => ?_⟩
    · show reflect f d = c
      rw [reflect_apply]
      exact hf'
    · rw [reflect_apply, neg_neg]

/-- **A coordinate may be pinned at any index, to any value.**  This is the
first fact in the lane that is not anchored at the origin. -/
theorem higmanGenerated_pinAt (d c : ℤ) : HigmanGenerated (pinAt d c) := by
  by_cases hd : 0 ≤ d
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = (n : ℤ) := ⟨d.toNat, by omega⟩
    rw [← sigmaOp_iterate_pinZero n c]
    exact higmanGenerated_sigmaOp_iterate n (higmanGenerated_pinZero' c)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = -(n : ℤ) := ⟨(-d).toNat, by omega⟩
    rw [← rhoOp_pinAt (n : ℤ) c, ← sigmaOp_iterate_pinZero n c]
    exact HigmanGenerated.rho
      (higmanGenerated_sigmaOp_iterate n (higmanGenerated_pinZero' c))

/-- A finite family of pins. -/
theorem higmanGenerated_pins (s : Finset ℤ) (v : ℤ → ℤ) :
    HigmanGenerated (⋂ i ∈ s, pinAt i (v i)) :=
  higmanGenerated_biInter s (fun i => pinAt i (v i)) fun i _ =>
    higmanGenerated_pinAt i (v i)

/-! ## 3.  Half-lines and windows -/

/-- The sequences vanishing strictly below `N`. -/
def vanishBelow (N : ℤ) : Set E := {f | ∀ i : ℤ, i < N → f i = 0}

/-- The sequences vanishing strictly above `N`. -/
def vanishAbove (N : ℤ) : Set E := {f | ∀ i : ℤ, N < i → f i = 0}

theorem piOp_Zset : piOp Zset = vanishBelow 1 := by
  ext f
  constructor
  · rintro ⟨g, hg, h⟩ i hi
    have hg' : g = 0 := hg
    rw [h i (by omega), hg']
    simp
  · intro h
    refine ⟨0, rfl, fun i hi => ?_⟩
    rw [h i (by omega)]
    simp

theorem zetaOp_vanishBelow_one : zetaOp (vanishBelow 1) = vanishBelow 0 := by
  ext f
  constructor
  · rintro ⟨g, hg, h⟩ i hi
    rw [h i (by omega)]
    exact hg i (by omega)
  · intro h
    have h' : ∀ i : ℤ, i < 0 → f i = 0 := h
    refine ⟨Finsupp.filter (fun j : ℤ => (1 : ℤ) ≤ j) f, ?_, ?_⟩
    · intro i hi
      rw [Finsupp.filter_apply, if_neg (by omega)]
    · intro i hi
      rw [Finsupp.filter_apply]
      by_cases hpos : (1 : ℤ) ≤ i
      · rw [if_pos hpos]
      · rw [if_neg hpos]
        exact h' i (by omega)

theorem higmanGenerated_vanishBelow_zero : HigmanGenerated (vanishBelow 0) := by
  rw [← zetaOp_vanishBelow_one, ← piOp_Zset]
  exact HigmanGenerated.zeta (HigmanGenerated.pi HigmanGenerated.zero)

/-- `σⁿ` moves a half-line `n` steps to the right. -/
theorem sigmaOp_iterate_vanishBelow (n : ℕ) (N : ℤ) :
    sigmaOp^[n] (vanishBelow N) = vanishBelow (N + n) := by
  ext f
  rw [mem_sigmaOp_iterate_iff]
  constructor
  · rintro ⟨g, hg, h⟩ i hi
    rw [h i]
    exact hg (i - n) (by omega)
  · intro h
    have h' : ∀ i : ℤ, i < N + n → f i = 0 := h
    obtain ⟨g, rfl⟩ := exists_shiftSeq_iterate n f
    refine ⟨g, ?_, fun i => shiftSeq_iterate_apply n g i⟩
    intro j hj
    have hj1 := h' (j + (n : ℤ)) (by omega)
    rw [shiftSeq_iterate_apply] at hj1
    have hjj : j + (n : ℤ) - (n : ℤ) = j := by ring
    rwa [hjj] at hj1

theorem sigmaOp_iterate_vanishAbove (n : ℕ) (N : ℤ) :
    sigmaOp^[n] (vanishAbove N) = vanishAbove (N + n) := by
  ext f
  rw [mem_sigmaOp_iterate_iff]
  constructor
  · rintro ⟨g, hg, h⟩ i hi
    rw [h i]
    exact hg (i - n) (by omega)
  · intro h
    have h' : ∀ i : ℤ, N + n < i → f i = 0 := h
    obtain ⟨g, rfl⟩ := exists_shiftSeq_iterate n f
    refine ⟨g, ?_, fun i => shiftSeq_iterate_apply n g i⟩
    intro j hj
    have hj1 := h' (j + (n : ℤ)) (by omega)
    rw [shiftSeq_iterate_apply] at hj1
    have hjj : j + (n : ℤ) - (n : ℤ) = j := by ring
    rwa [hjj] at hj1

theorem rhoOp_vanishBelow (N : ℤ) : rhoOp (vanishBelow N) = vanishAbove (-N) := by
  ext f
  constructor
  · rintro ⟨g, hg, h⟩ i hi
    rw [h i]
    exact hg (-i) (by omega)
  · intro h
    have h' : ∀ i : ℤ, -N < i → f i = 0 := h
    refine ⟨reflect f, ?_, fun i => ?_⟩
    · intro j hj
      rw [reflect_apply]
      exact h' (-j) (by omega)
    · rw [reflect_apply, neg_neg]

theorem rhoOp_vanishAbove (N : ℤ) : rhoOp (vanishAbove N) = vanishBelow (-N) := by
  ext f
  constructor
  · rintro ⟨g, hg, h⟩ i hi
    rw [h i]
    exact hg (-i) (by omega)
  · intro h
    have h' : ∀ i : ℤ, i < -N → f i = 0 := h
    refine ⟨reflect f, ?_, fun i => ?_⟩
    · intro j hj
      rw [reflect_apply]
      exact h' (-j) (by omega)
    · rw [reflect_apply, neg_neg]

theorem higmanGenerated_vanishAbove_zero : HigmanGenerated (vanishAbove 0) := by
  have h := HigmanGenerated.rho higmanGenerated_vanishBelow_zero
  rwa [rhoOp_vanishBelow, neg_zero] at h

/-- **Every half-line support condition is generated.** -/
theorem higmanGenerated_vanishBelow (N : ℤ) : HigmanGenerated (vanishBelow N) := by
  by_cases hN : 0 ≤ N
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = (n : ℤ) := ⟨N.toNat, by omega⟩
    have h := higmanGenerated_sigmaOp_iterate n higmanGenerated_vanishBelow_zero
    rwa [sigmaOp_iterate_vanishBelow, zero_add] at h
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = -(n : ℤ) := ⟨(-N).toNat, by omega⟩
    have h := higmanGenerated_sigmaOp_iterate n higmanGenerated_vanishAbove_zero
    rw [sigmaOp_iterate_vanishAbove, zero_add] at h
    have h2 := HigmanGenerated.rho h
    rwa [rhoOp_vanishAbove] at h2

theorem higmanGenerated_vanishAbove (N : ℤ) : HigmanGenerated (vanishAbove N) := by
  have h := HigmanGenerated.rho (higmanGenerated_vanishBelow (-N))
  rwa [rhoOp_vanishBelow, neg_neg] at h

/-- The sequences supported in the window `[a, b]`. -/
theorem higmanGenerated_window (a b : ℤ) :
    HigmanGenerated (vanishBelow a ∩ vanishAbove b) :=
  HigmanGenerated.inter (higmanGenerated_vanishBelow a) (higmanGenerated_vanishAbove b)

/-! ## 4.  Singletons, and every finite set -/

/-- The support of a finitely supported sequence lies in a window. -/
theorem exists_support_bounds (f₀ : E) :
    ∃ a b : ℤ, (∀ i : ℤ, i < a → f₀ i = 0) ∧ (∀ i : ℤ, b < i → f₀ i = 0) := by
  have hne : (insert (0 : ℤ) f₀.support).Nonempty := ⟨0, Finset.mem_insert_self 0 _⟩
  refine ⟨(insert (0 : ℤ) f₀.support).min' hne,
    (insert (0 : ℤ) f₀.support).max' hne, ?_, ?_⟩
  · intro i hi
    by_contra hzero
    have hmem : i ∈ insert (0 : ℤ) f₀.support :=
      Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr hzero)
    have hle : (insert (0 : ℤ) f₀.support).min' hne ≤ i := Finset.min'_le _ i hmem
    omega
  · intro i hi
    by_contra hzero
    have hmem : i ∈ insert (0 : ℤ) f₀.support :=
      Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr hzero)
    have hle : i ≤ (insert (0 : ℤ) f₀.support).max' hne := Finset.le_max' _ i hmem
    omega

/-- **A single sequence is cut out by two half-lines and finitely many pins.** -/
theorem singleton_eq_inter (f₀ : E) (a b : ℤ)
    (ha : ∀ i : ℤ, i < a → f₀ i = 0) (hb : ∀ i : ℤ, b < i → f₀ i = 0) :
    ({f₀} : Set E) = (vanishBelow a ∩ vanishAbove b) ∩
      ⋂ i ∈ Finset.Icc a b, pinAt i (f₀ i) := by
  ext f
  constructor
  · rintro rfl
    exact ⟨⟨ha, hb⟩, Set.mem_iInter.mpr fun i => Set.mem_iInter.mpr fun _ => rfl⟩
  · rintro ⟨⟨hbelow, habove⟩, hpins⟩
    have hbelow' : ∀ i : ℤ, i < a → f i = 0 := hbelow
    have habove' : ∀ i : ℤ, b < i → f i = 0 := habove
    have hpins' : ∀ i : ℤ, i ∈ Finset.Icc a b → f i = f₀ i := fun i hi =>
      Set.mem_iInter.mp (Set.mem_iInter.mp hpins i) hi
    show f = f₀
    refine Finsupp.ext fun i => ?_
    by_cases hi : i < a
    · rw [hbelow' i hi, ha i hi]
    · by_cases hi2 : b < i
      · rw [habove' i hi2, hb i hi2]
      · exact hpins' i (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

/-- **Every one-point set is generated.**  `Higman/GeneratedValue.lean` reaches
the one-point sets at the origin; with pins at every index and the two
half-lines, every one-point set whatever is reached. -/
theorem higmanGenerated_singleton (f₀ : E) : HigmanGenerated ({f₀} : Set E) := by
  obtain ⟨a, b, ha, hb⟩ := exists_support_bounds f₀
  rw [singleton_eq_inter f₀ a b ha hb]
  exact HigmanGenerated.inter (higmanGenerated_window a b)
    (higmanGenerated_pins (Finset.Icc a b) (fun i => f₀ i))

/-- **Every finite set of sequences is generated.**  So the residue of Higman's
Theorem 3 is exactly the passage from finite unions to computably enumerated
ones. -/
theorem higmanGenerated_of_finite {B : Set E} (hB : B.Finite) : HigmanGenerated B := by
  have hunion : B = ⋃ f ∈ hB.toFinset, ({f} : Set E) := by
    ext g
    constructor
    · intro hg
      exact Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr
        ⟨(Set.Finite.mem_toFinset hB).mpr hg, rfl⟩⟩
    · intro hg
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hg
      obtain ⟨hxs, hgx⟩ := Set.mem_iUnion.mp hx
      have hgx' : g = x := hgx
      rw [hgx']
      exact (Set.Finite.mem_toFinset hB).mp hxs
  rw [hunion]
  exact @higmanGenerated_biUnion E (fun _ _ => Classical.propDecidable _) hB.toFinset
    (fun f => ({f} : Set E)) fun f _ => higmanGenerated_singleton f

/-! ## 5.  Freeing the negative half -/

/-- **`ρ π ρ` frees the negative coordinates.**  `Higman/AgreeClosure.lean` reads
`π` as agreement on the coordinates `i ≤ 0` (`Agree.piOp_eq_agreeOp`); this is
the mirror statement, agreement on the coordinates `0 ≤ i`.  With `π` it makes a
condition imposable on one half-line only, which is what an anchored
construction needs. -/
theorem rhoOp_piOp_rhoOp (B : Set E) :
    rhoOp (piOp (rhoOp B)) = Agree.agreeOp (fun i : ℤ => 0 ≤ i) B := by
  ext f
  constructor
  · rintro ⟨h, ⟨k, ⟨g, hg, hkg⟩, hhk⟩, hfh⟩
    refine ⟨g, hg, fun i hi => ?_⟩
    have hi' : (0 : ℤ) ≤ i := hi
    rw [hfh i, hhk (-i) (by omega), hkg (-i), neg_neg]
  · rintro ⟨g, hg, hfg⟩
    have hfg' : ∀ i : ℤ, 0 ≤ i → f i = g i := hfg
    refine ⟨reflect f, ?_, ?_⟩
    · refine ⟨reflect g, ?_, ?_⟩
      · exact ⟨g, hg, fun i => reflect_apply g i⟩
      · intro i hi
        rw [reflect_apply, reflect_apply]
        exact hfg' (-i) (by omega)
    · intro i
      rw [reflect_apply, neg_neg]

theorem higmanGenerated_agreeOp_nonneg {B : Set E} (h : HigmanGenerated B) :
    HigmanGenerated (Agree.agreeOp (fun i : ℤ => 0 ≤ i) B) := by
  rw [← rhoOp_piOp_rhoOp]
  exact HigmanGenerated.rho (HigmanGenerated.pi (HigmanGenerated.rho h))

/-! ## 6.  Iterating `θ`, and the projection of a trace -/

theorem thetaSeq_iterate_apply (t : ℕ) (g : E) (i : ℤ) :
    thetaSeq^[t] g i = g (2 ^ t * i) := by
  induction t generalizing i with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', thetaSeq_apply, ih]
      congr 1
      ring

/-- **`θᵗ` reads the coordinates divisible by `2ᵗ`.**  This is the compression
that turns a computation in blocks of width `2ᵗ` into its first track. -/
theorem mem_thetaOp_iterate_iff (t : ℕ) (B : Set E) (f : E) :
    f ∈ thetaOp^[t] B ↔ ∃ g ∈ B, ∀ i : ℤ, f i = g (2 ^ t * i) := by
  induction t generalizing f with
  | zero =>
      simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
      constructor
      · intro hf
        exact ⟨f, hf, fun _ => rfl⟩
      · rintro ⟨g, hg, h⟩
        have hfg : f = g := Finsupp.ext fun i => h i
        rwa [hfg]
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      constructor
      · rintro ⟨h, hh, hfh⟩
        obtain ⟨g, hg, hhg⟩ := (ih h).mp hh
        refine ⟨g, hg, fun i => ?_⟩
        rw [hfh i, hhg (2 * i)]
        congr 1
        ring
      · rintro ⟨g, hg, hfg⟩
        refine ⟨thetaSeq^[n] g,
          (ih _).mpr ⟨g, hg, fun j => thetaSeq_iterate_apply n g j⟩, fun i => ?_⟩
        rw [thetaSeq_iterate_apply, hfg i]
        congr 1
        ring

theorem higmanGenerated_thetaOp_iterate (t : ℕ) {B : Set E} (h : HigmanGenerated B) :
    HigmanGenerated (thetaOp^[t] B) := by
  induction t with
  | zero => simpa using h
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact HigmanGenerated.theta ih

/-- **The projection step.**  A generated set of sequences whose `2ᵗ`-th
coordinates are exactly the members of `C` puts `C` in the family. -/
theorem higmanGenerated_of_thetaProjection {t : ℕ} {T C : Set E}
    (hT : HigmanGenerated T)
    (hproj : ∀ f : E, (∃ g ∈ T, ∀ i : ℤ, f i = g (2 ^ t * i)) ↔ f ∈ C) :
    HigmanGenerated C := by
  have hC : C = thetaOp^[t] T := by
    ext f
    rw [mem_thetaOp_iterate_iff]
    exact (hproj f).symm
  rw [hC]
  exact higmanGenerated_thetaOp_iterate t hT

/-- **The whole trace construction, in one statement.**  `A` is the relation
between adjacent `k`-blocks, `D` the anchoring conditions, and the projection
reads the first track of every block.  Everything in it is proved; supplying
`A` and `D` for a given enumeration is what remains of Higman's Section 2. -/
theorem higmanGenerated_of_transitionProjection {t k : ℕ} (hk : 0 < k)
    {A D C : Set E} (hA : HigmanGenerated A) (hD : HigmanGenerated D)
    (hproj : ∀ f : E,
      (∃ g ∈ transitionSet k A ∩ D, ∀ i : ℤ, f i = g (2 ^ t * i)) ↔ f ∈ C) :
    HigmanGenerated C :=
  higmanGenerated_of_thetaProjection (t := t)
    (HigmanGenerated.inter (higmanGenerated_transitionSet k hk hA) hD) hproj

end Seq

/-! ## 7.  The remaining input, and the reduction -/

/-- **Input: the last step of Higman's Section 2.**  The family Higman builds
from `Z` and `S` is closed under unions indexed by a total computable
enumeration.

This is all that `HigmanTheoremThree` still owes.  Finite unions are proved
(`Seq.higmanGenerated_of_finite`), the empty set is proved
(`Seq.higmanGenerated_empty`), and `exists_computable_enumeration` --- Higman's
Lemma 2.8, with the hypothesis his printed statement omits --- turns every
nonempty recursively enumerable set into exactly such a range.

**Nothing inhabits this structure.** -/
structure EnumeratedRangeGenerated where
  /-- The range of a total computable enumeration of codes is generated. -/
  range : ∀ c : ℕ → List (ℤ × ℤ), Computable c →
    Seq.HigmanGenerated {g : Seq.E | ∃ r : ℕ, seqOfList (c r) = g}

/-- **Every recursively enumerable set is generated, from the enumerated-range
closure.**  The empty case is unconditional and is not an afterthought: Lemma
2.8 fails there, so the split is forced. -/
theorem higmanGenerated_of_REset (h : EnumeratedRangeGenerated) (B : Set Seq.E)
    (hB : REset B) : Seq.HigmanGenerated B := by
  rcases Set.eq_empty_or_nonempty B with rfl | hne
  · exact Seq.higmanGenerated_empty
  · obtain ⟨c, hc, hspec⟩ := exists_computable_enumeration hB hne
    have hBset : B = {g : Seq.E | ∃ r : ℕ, seqOfList (c r) = g} := by
      ext g
      exact hspec g
    rw [hBset]
    exact h.range c hc

/-- **Higman's Section 2, from its last step.** -/
theorem higmanTheoremThree_of_enumeratedRange (h : EnumeratedRangeGenerated) :
    HigmanTheoremThree where
  generated := higmanGenerated_of_REset h

/-- **Chiodo Theorem 3.10 from four inputs, with the Section 2 input sharpened.**
The count is unchanged; what changes is that the second input is now the single
closure property `EnumeratedRangeGenerated` rather than the whole of Higman's
Section 2. -/
theorem statement_of_four_enumerated (h₁ : OperationClosures)
    (h₂ : EnumeratedRangeGenerated) (h₃ : TransportSectionFive)
    (h₄ : BridgeRecursive) : ChiodoBelegradek.Statement :=
  statement_of_four h₁ (higmanTheoremThree_of_enumeratedRange h₂) h₃ h₄

end Higman
end GroupApproximation
