import GroupApproximation.Higman.EnumeratedRangeTrace

/-!
# The variable calculus: freeing, projecting, permuting and padding a coordinate

`Higman.BoundedWindowRE` (`Higman/EnumeratedRangeTrace.lean`) asks for every
recursively enumerable set of sequences supported in a fixed finite window.  A
relation of arity `n` is exactly such a set --- a subset of
`Seq.windowSupport n` --- and building one from the nine operations means being
able to do to *any* coordinate of the window what the operations do to the
origin.

That is the whole content of this module, and it has a single bottleneck.

## The bottleneck

`ζ` frees the coordinate `0`, and nothing else in Higman's list frees a
coordinate anywhere.  `π` frees a half-line, `ω` speaks about blocks, and the
lattice operations do not move anything.  So the one thing to prove is that the
coordinate `ζ` frees can be moved, and the move is a conjugation:

    σ ∘ (agreement on `p`) ∘ σ⁻¹  =  agreement on `p(· - 1)` ,

which is `Seq.sigmaOp_agreeOp_sigmaInvOp`.  Iterating it `n` times turns `ζ`
into `Seq.freeAt n`, which frees the coordinate `n`
(`Seq.freeAt_eq`), and reflecting with `ρ` reaches the negative coordinates as
well (`Seq.higmanGenerated_agreeOp_ne`).  `σ⁻¹` is itself `ρ σ ρ`
(`Seq.sigmaInvOp`), so no operation outside Higman's list is used anywhere.

## What everything else costs, once that is available

Nothing.  Freeing the coordinate `n` and then re-imposing a window is

* **existential projection** when the window is `[0, n)` --- the freed
  coordinate is the one being quantified away, and the remaining coordinates
  are forced back into the smaller window (`Seq.existsLast`);
* **padding** when the window is `[0, n + 1)` --- the freed coordinate is a new
  dummy variable (`Seq.padLast`).

The two definitions differ only in the width of the window they intersect with,
which is the reason freeing is the bottleneck and not one of three separate
problems.

## Canonical variable order, and where `τ` is not

Relations are built in a **canonical variable order**: a condition is placed at
the coordinate it belongs to when it is constructed, by `σ`-conjugating the
index-`0` case, and coordinates are never permuted afterwards.  Section 3 is
that discipline for `ζ`; `Seq.conjAt` is it for an arbitrary agreement
operation, which is the general form of the engine.

This module accordingly uses only `ζ`, `π`, `ρ`, `σ` and the lattice
operations, and **`τ` appears nowhere in it**.  That includes the quantifier
over a variable that is not the last one: `Seq.existsAt` projects such a
coordinate away by freeing it and pinning it to zero, leaving a hole rather than
compacting the window.  Compacting --- shifting the coordinates above the
quantified one down by one --- is exactly what would need a transposition, and
it is exactly what is avoided.

An earlier draft carried a transposition calculus, `swapAt d`, built from `τ` by
the same conjugation and merely marked as off the chain.  It has been
**deleted**.  It held the last use of the `τ` constructor in the repository; an
unused consumer of an open leaf is precisely what a removal audit trips on, and
every module importing this one would have carried it along.
`Higman.TauRouteC` and `Higman.SwapWitnessTower` hold the record of what `τ`
would have bought.  Nothing in use was lost --- it had no consumer, here or
anywhere, at the time it was removed.

## The arity-`n` notion

`Seq.IsArity n R` says `R ⊆ Seq.windowSupport n`, and that is the definition of
a relation on `ℤⁿ` used throughout: the `n` coordinates are the values at the
indices `0, …, n - 1` and every other index is pinned to zero.

That is the *set-level* notion, and it is the only one this module needs.  The
tuple carrier is `Fin n → ℤ` and it lives elsewhere, because it is what has to
be `Primcodable` for the computability transfer, which nothing here touches:
`Higman.HigmanCodingDictionary` owns the bijection (`Seq.windowCoords`,
`Seq.coordSeq`, `Seq.windowEquiv`) and `Higman.HigmanAtoms` states its relations
as `Seq.winRel`.  Both fit this module without a bridge lemma --- `winRel_subset`
*is* `IsArity` of a `winRel`, definitionally, and so composes directly with
`IsArity.mono`, `IsArity.inter_left`, `padLast` and the rest.

`Seq.winSeq` is a convenience of this file only: it converts a tuple presented
as a function `ℤ → ℤ`, which is the shape the coordinate arithmetic below wants
and is deliberately *not* the arity carrier.  `Seq.winSeq_eq_self` says nothing
is lost in the conversion.  The statements that matter are carrier-free anyway:
`mem_existsLast_iff`, `mem_padLast_iff` and `mem_existsAt_iff` speak only of
`f + Finsupp.single (k : ℤ) y`, so they transfer to any carrier that can say
what appending a coordinate does.

Everything in this module is unconditional: it consumes only the constructors
of `Seq.HigmanGenerated` and the calculus already proved in
`Higman/TheoremThreeAssembly.lean` and `Higman/EnumeratedRange.lean`, and it
adds no input.

## Reference

Higman 1961, Section 2.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

/-! ## 1.  Undoing the shift on a single sequence

Every conjugation below needs, for a given sequence, the sequence read one step
later.  The shift is surjective (`exists_shiftSeq_iterate`), so this is a
restatement and not a construction. -/

/-- The sequence read one step to the right. -/
theorem exists_unshift (f : E) : ∃ h : E, ∀ i : ℤ, h i = f (i + 1) := by
  obtain ⟨h, hh⟩ := exists_shiftSeq_iterate 1 f
  rw [Function.iterate_one] at hh
  refine ⟨h, fun i => ?_⟩
  have hi : shiftSeq h (i + 1) = h (i + 1 - 1) := shiftSeq_apply h (i + 1)
  rw [hh, show i + 1 - 1 = i from by ring] at hi
  exact hi.symm

/-- Agreement depends on the index predicate only through its truth values. -/
theorem agreeOp_congr {p q : ℤ → Prop} (hpq : ∀ i : ℤ, p i ↔ q i) (B : Set E) :
    Agree.agreeOp p B = Agree.agreeOp q B := by
  have hfun : p = q := funext fun i => propext (hpq i)
  rw [hfun]

/-! ## 2.  Conjugating an agreement condition

The single step, and its mirror.  `σ` moves the condition one index to the
right; `ρ` reflects it. -/

/-- **The single step.**  Conjugating an agreement condition by the shift
translates the index predicate.  This is the one fact the whole module rests
on. -/
theorem sigmaOp_agreeOp_sigmaInvOp (p : ℤ → Prop) (B : Set E) :
    sigmaOp (Agree.agreeOp p (sigmaInvOp B))
      = Agree.agreeOp (fun i : ℤ => p (i - 1)) B := by
  ext f
  rw [mem_sigmaOp_iff]
  constructor
  · rintro ⟨h, ⟨k, hk, hhk⟩, hfh⟩
    rw [mem_sigmaInvOp_iff] at hk
    obtain ⟨g, hg, hkg⟩ := hk
    refine ⟨g, hg, fun i hi => ?_⟩
    have hi' : p (i - 1) := hi
    rw [hfh i, hhk (i - 1) hi', hkg (i - 1)]
    congr 1
    ring
  · rintro ⟨g, hg, hfg⟩
    have hfg' : ∀ i : ℤ, p (i - 1) → f i = g i := hfg
    obtain ⟨h, hh⟩ := exists_unshift f
    obtain ⟨k, hk⟩ := exists_unshift g
    refine ⟨h, ⟨k, ?_, fun i hi => ?_⟩, fun i => ?_⟩
    · rw [mem_sigmaInvOp_iff]
      exact ⟨g, hg, hk⟩
    · rw [hh i, hk i]
      exact hfg' (i + 1) (by rw [show i + 1 - 1 = i from by ring]; exact hi)
    · rw [hh (i - 1), show i - 1 + 1 = i from by ring]

/-- **The mirror step.**  Conjugating an agreement condition by the reflection
reflects the index predicate. -/
theorem rhoOp_agreeOp_rhoOp (p : ℤ → Prop) (B : Set E) :
    rhoOp (Agree.agreeOp p (rhoOp B)) = Agree.agreeOp (fun i : ℤ => p (-i)) B := by
  ext f
  constructor
  · rintro ⟨h, ⟨k, ⟨g, hg, hkg⟩, hhk⟩, hfh⟩
    refine ⟨g, hg, fun i hi => ?_⟩
    have hi' : p (-i) := hi
    rw [hfh i, hhk (-i) hi', hkg (-i), neg_neg]
  · rintro ⟨g, hg, hfg⟩
    have hfg' : ∀ i : ℤ, p (-i) → f i = g i := hfg
    refine ⟨reflect f, ⟨reflect g, ⟨g, hg, fun i => reflect_apply g i⟩,
      fun i hi => ?_⟩, fun i => ?_⟩
    · rw [reflect_apply, reflect_apply]
      exact hfg' (-i) (by rw [neg_neg]; exact hi)
    · rw [reflect_apply, neg_neg]

/-! ## 3.  Freeing an arbitrary coordinate -/

/-- **`ζ` moved to the coordinate `n`.**  Conjugate the liberation of the origin
by the `n`-fold shift. -/
noncomputable def freeAt (n : ℕ) (B : Set E) : Set E :=
  sigmaOp^[n] (zetaOp (sigmaInvOp^[n] B))

theorem freeAt_zero (B : Set E) : freeAt 0 B = zetaOp B := by
  unfold freeAt
  rw [Function.iterate_zero, id_eq, Function.iterate_zero, id_eq]

theorem freeAt_succ (n : ℕ) (B : Set E) :
    freeAt (n + 1) B = sigmaOp (freeAt n (sigmaInvOp B)) := by
  unfold freeAt
  rw [Function.iterate_succ_apply' sigmaOp n, Function.iterate_succ_apply sigmaInvOp n]

/-- **Freeing the coordinate `n`.**  `ζ` frees only the origin; this frees any
coordinate, and it is the fact every later construction consumes. -/
theorem freeAt_eq (n : ℕ) (B : Set E) :
    freeAt n B = Agree.agreeOp (fun i : ℤ => i ≠ (n : ℤ)) B := by
  induction n generalizing B with
  | zero =>
      rw [freeAt_zero, Agree.zetaOp_eq_agreeOp]
      refine agreeOp_congr (fun i => ?_) B
      show i ≠ (0 : ℤ) ↔ i ≠ ((0 : ℕ) : ℤ)
      constructor
      · intro h hne
        omega
      · intro h hne
        omega
  | succ n ih =>
      rw [freeAt_succ, ih (sigmaInvOp B), sigmaOp_agreeOp_sigmaInvOp]
      refine agreeOp_congr (fun i => ?_) B
      show i - 1 ≠ (n : ℤ) ↔ i ≠ ((n + 1 : ℕ) : ℤ)
      constructor
      · intro h hne
        omega
      · intro h hne
        omega

theorem mem_freeAt_iff (n : ℕ) (B : Set E) (f : E) :
    f ∈ freeAt n B ↔ ∃ g ∈ B, ∀ i : ℤ, i ≠ (n : ℤ) → f i = g i := by
  constructor
  · intro hf
    rw [freeAt_eq] at hf
    exact hf
  · intro hf
    rw [freeAt_eq]
    exact hf

theorem higmanGenerated_sigmaInvOp_iterate (n : ℕ) {B : Set E} (h : HigmanGenerated B) :
    HigmanGenerated (sigmaInvOp^[n] B) := by
  induction n with
  | zero => simpa using h
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact higmanGenerated_sigmaInvOp ih

theorem higmanGenerated_freeAt (n : ℕ) {B : Set E} (h : HigmanGenerated B) :
    HigmanGenerated (freeAt n B) := by
  unfold freeAt
  exact higmanGenerated_sigmaOp_iterate n
    (HigmanGenerated.zeta (higmanGenerated_sigmaInvOp_iterate n h))

theorem higmanGenerated_agreeOp_ne_natCast (n : ℕ) {B : Set E} (h : HigmanGenerated B) :
    HigmanGenerated (Agree.agreeOp (fun i : ℤ => i ≠ (n : ℤ)) B) := by
  rw [← freeAt_eq]
  exact higmanGenerated_freeAt n h

/-- **Any coordinate whatever may be freed.**  The non-negative ones by the
shift, the negative ones by reflecting those. -/
theorem higmanGenerated_agreeOp_ne (d : ℤ) {B : Set E} (h : HigmanGenerated B) :
    HigmanGenerated (Agree.agreeOp (fun i : ℤ => i ≠ d) B) := by
  by_cases hd : 0 ≤ d
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = (n : ℤ) := ⟨d.toNat, by omega⟩
    exact higmanGenerated_agreeOp_ne_natCast n h
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = -(n : ℤ) := ⟨(-d).toNat, by omega⟩
    have heq : Agree.agreeOp (fun i : ℤ => i ≠ -(n : ℤ)) B
        = rhoOp (Agree.agreeOp (fun i : ℤ => i ≠ (n : ℤ)) (rhoOp B)) := by
      rw [rhoOp_agreeOp_rhoOp]
      refine agreeOp_congr (fun i => ?_) B
      show i ≠ -(n : ℤ) ↔ -i ≠ (n : ℤ)
      constructor
      · intro hi hne
        omega
      · intro hi hne
        omega
    rw [heq]
    exact HigmanGenerated.rho
      (higmanGenerated_agreeOp_ne_natCast n (HigmanGenerated.rho h))

/-! ## 3b.  The engine, in general

`freeAt` is one instance of a single construction: take an agreement operation
anchored at the origin and move it to the index `n` by `σ`-conjugation.  That is
the canonical-variable-order discipline, and it is worth having in general in
the index predicate, because every later work item places its conditions this
way rather than permuting them into position afterwards. -/

/-- The agreement operation `p`, moved to the index `n` by `σ`-conjugation. -/
noncomputable def conjAt (n : ℕ) (p : ℤ → Prop) (B : Set E) : Set E :=
  sigmaOp^[n] (Agree.agreeOp p (sigmaInvOp^[n] B))

theorem conjAt_zero (p : ℤ → Prop) (B : Set E) :
    conjAt 0 p B = Agree.agreeOp p B := by
  unfold conjAt
  rw [Function.iterate_zero, id_eq, Function.iterate_zero, id_eq]

theorem conjAt_succ (n : ℕ) (p : ℤ → Prop) (B : Set E) :
    conjAt (n + 1) p B = sigmaOp (conjAt n p (sigmaInvOp B)) := by
  unfold conjAt
  rw [Function.iterate_succ_apply' sigmaOp n, Function.iterate_succ_apply sigmaInvOp n]

/-- **Conjugating by `σⁿ` translates the index predicate by `n`.** -/
theorem conjAt_eq (n : ℕ) (p : ℤ → Prop) (B : Set E) :
    conjAt n p B = Agree.agreeOp (fun i : ℤ => p (i - (n : ℤ))) B := by
  induction n generalizing B with
  | zero =>
      rw [conjAt_zero]
      refine agreeOp_congr (fun i => ?_) B
      show p i ↔ p (i - ((0 : ℕ) : ℤ))
      rw [show i - ((0 : ℕ) : ℤ) = i from by omega]
  | succ n ih =>
      rw [conjAt_succ, ih (sigmaInvOp B), sigmaOp_agreeOp_sigmaInvOp]
      refine agreeOp_congr (fun i => ?_) B
      show p (i - 1 - (n : ℤ)) ↔ p (i - ((n + 1 : ℕ) : ℤ))
      rw [show i - 1 - (n : ℤ) = i - ((n + 1 : ℕ) : ℤ) from by omega]

theorem mem_conjAt_iff (n : ℕ) (p : ℤ → Prop) (B : Set E) (f : E) :
    f ∈ conjAt n p B ↔ ∃ g ∈ B, ∀ i : ℤ, p (i - (n : ℤ)) → f i = g i := by
  constructor
  · intro hf
    rw [conjAt_eq] at hf
    exact hf
  · intro hf
    rw [conjAt_eq]
    exact hf

/-- Freeing a coordinate is the case `p = (· ≠ 0)`. -/
theorem freeAt_eq_conjAt (n : ℕ) (B : Set E) :
    freeAt n B = conjAt n (fun i : ℤ => i ≠ 0) B := by
  unfold freeAt conjAt
  rw [Agree.zetaOp_eq_agreeOp]

/-- **Generation transports along the conjugation**, given it for the operation
at the origin. -/
theorem higmanGenerated_conjAt (n : ℕ) {p : ℤ → Prop}
    (hp : ∀ C : Set E, HigmanGenerated C → HigmanGenerated (Agree.agreeOp p C))
    {B : Set E} (h : HigmanGenerated B) : HigmanGenerated (conjAt n p B) := by
  unfold conjAt
  exact higmanGenerated_sigmaOp_iterate n
    (hp _ (higmanGenerated_sigmaInvOp_iterate n h))

/-! ## 4.  Relations of a fixed arity

A relation on `ℤⁿ` is a set of sequences supported in the window `[0, n)`: the
`n` arguments are the values at the indices `0, …, n - 1`, and every other index
carries a zero that no operation is allowed to disturb.  `windowSupport` is
generated (`higmanGenerated_windowSupport`), so imposing the arity costs one
intersection. -/

/-- **An arity-`n` relation**: a set of sequences supported in `[0, n)`. -/
def IsArity (n : ℕ) (R : Set E) : Prop := R ⊆ windowSupport n

theorem isArity_windowSupport (n : ℕ) : IsArity n (windowSupport n) := by
  intro _ hf
  exact hf

/-- A relation of arity `n` is one of arity `m` for any larger `m`, with the
extra coordinates pinned to zero. -/
theorem IsArity.mono {n m : ℕ} (hnm : n ≤ m) {R : Set E} (hR : IsArity n R) :
    IsArity m R := by
  intro f hf
  obtain ⟨h1, h2⟩ := (mem_windowSupport_iff n f).mp (hR hf)
  exact (mem_windowSupport_iff m f).mpr ⟨h1, fun i hi => h2 i (by omega)⟩

theorem IsArity.inter_left {n : ℕ} {R S : Set E} (hR : IsArity n R) :
    IsArity n (R ∩ S) := by
  intro _ hf
  exact hR hf.1

theorem IsArity.union {n : ℕ} {R S : Set E} (hR : IsArity n R) (hS : IsArity n S) :
    IsArity n (R ∪ S) := by
  intro _ hf
  rcases hf with hf | hf
  · exact hR hf
  · exact hS hf

/-- Cutting a set of sequences down to arity `n`. -/
def restrictArity (n : ℕ) (R : Set E) : Set E := R ∩ windowSupport n

theorem mem_restrictArity_iff (n : ℕ) (R : Set E) (f : E) :
    f ∈ restrictArity n R ↔ f ∈ R ∧ f ∈ windowSupport n := Iff.rfl

theorem isArity_restrictArity (n : ℕ) (R : Set E) : IsArity n (restrictArity n R) := by
  intro _ hf
  exact hf.2

theorem higmanGenerated_restrictArity (n : ℕ) {R : Set E} (h : HigmanGenerated R) :
    HigmanGenerated (restrictArity n R) := by
  unfold restrictArity
  exact HigmanGenerated.inter h (higmanGenerated_windowSupport n)

/-- Cutting down to arity `n` commutes with conjunction. -/
theorem restrictArity_inter (n : ℕ) (R S : Set E) :
    restrictArity n (R ∩ S) = restrictArity n R ∩ restrictArity n S := by
  unfold restrictArity
  ext f
  constructor
  · rintro ⟨⟨hR, hS⟩, hw⟩
    exact ⟨⟨hR, hw⟩, hS, hw⟩
  · rintro ⟨⟨hR, hw⟩, hS, _⟩
    exact ⟨⟨hR, hS⟩, hw⟩

/-- Cutting down to arity `n` commutes with disjunction. -/
theorem restrictArity_union (n : ℕ) (R S : Set E) :
    restrictArity n (R ∪ S) = restrictArity n R ∪ restrictArity n S := by
  unfold restrictArity
  ext f
  constructor
  · rintro ⟨hRS, hw⟩
    rcases hRS with hR | hS
    · exact Or.inl ⟨hR, hw⟩
    · exact Or.inr ⟨hS, hw⟩
  · rintro (⟨hR, hw⟩ | ⟨hS, hw⟩)
    · exact ⟨Or.inl hR, hw⟩
    · exact ⟨Or.inr hS, hw⟩

/-! ## 5.  Tuples

`winSeq n x` is the sequence representing the tuple `x` read on `[0, n)`.  It is
the bridge between a relation stated coordinate-wise and the set of sequences
that the operations act on. -/

/-- The sequence carrying the values of `x` on the window `[0, n)` and zero
elsewhere. -/
noncomputable def winSeq (n : ℕ) (x : ℤ → ℤ) : E :=
  Finsupp.onFinset (Finset.Ico (0 : ℤ) (n : ℤ))
    (fun i => if i ∈ Finset.Ico (0 : ℤ) (n : ℤ) then x i else 0)
    (by
      intro i hi
      by_contra hcon
      rw [if_neg hcon] at hi
      exact hi rfl)

theorem winSeq_apply (n : ℕ) (x : ℤ → ℤ) (i : ℤ) :
    winSeq n x i = if i ∈ Finset.Ico (0 : ℤ) (n : ℤ) then x i else 0 := by
  simp only [winSeq, Finsupp.onFinset_apply]

theorem winSeq_apply_of_mem (n : ℕ) (x : ℤ → ℤ) {i : ℤ} (h0 : 0 ≤ i)
    (hn : i < (n : ℤ)) : winSeq n x i = x i := by
  rw [winSeq_apply, if_pos (Finset.mem_Ico.mpr ⟨h0, hn⟩)]

theorem winSeq_mem_windowSupport (n : ℕ) (x : ℤ → ℤ) :
    winSeq n x ∈ windowSupport n := by
  refine (mem_windowSupport_iff n _).mpr ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hmem : i ∉ Finset.Ico (0 : ℤ) (n : ℤ) := by
      rw [Finset.mem_Ico]
      omega
    rw [winSeq_apply, if_neg hmem]
  · have hmem : i ∉ Finset.Ico (0 : ℤ) (n : ℤ) := by
      rw [Finset.mem_Ico]
      omega
    rw [winSeq_apply, if_neg hmem]

/-- **A window-supported sequence is the tuple of its own coordinates.**  So no
information is lost by describing an arity-`n` relation coordinate-wise. -/
theorem winSeq_eq_self {n : ℕ} {x : ℤ → ℤ} {f : E} (hf : f ∈ windowSupport n)
    (hx : ∀ i : ℤ, 0 ≤ i → i < (n : ℤ) → x i = f i) : winSeq n x = f := by
  obtain ⟨h1, h2⟩ := (mem_windowSupport_iff n f).mp hf
  refine Finsupp.ext fun i => ?_
  rw [winSeq_apply]
  by_cases hi : i ∈ Finset.Ico (0 : ℤ) (n : ℤ)
  · have hb := Finset.mem_Ico.mp hi
    rw [if_pos hi]
    exact hx i hb.1 hb.2
  · rw [if_neg hi]
    rw [Finset.mem_Ico] at hi
    by_cases hneg : i < 0
    · exact (h1 i hneg).symm
    · exact (h2 i (by omega)).symm

/-- **Extending a tuple by one coordinate.**  Adding a multiple of the basis
vector at `n` is the same as widening the window and writing the new value
there. -/
theorem winSeq_add_single (n : ℕ) (x : ℤ → ℤ) (y : ℤ) :
    winSeq n x + Finsupp.single (n : ℤ) y
      = winSeq (n + 1) (fun i => if i = (n : ℤ) then y else x i) := by
  refine Finsupp.ext fun i => ?_
  rw [Finsupp.add_apply, Finsupp.single_apply, winSeq_apply, winSeq_apply]
  by_cases hi : i = (n : ℤ)
  · have h1 : i ∉ Finset.Ico (0 : ℤ) (n : ℤ) := fun hc =>
      absurd (Finset.mem_Ico.mp hc).2 (by omega)
    have h2 : i ∈ Finset.Ico (0 : ℤ) ((n + 1 : ℕ) : ℤ) := Finset.mem_Ico.mpr (by omega)
    rw [if_neg h1, if_pos hi.symm, if_pos h2, if_pos hi, zero_add]
  · by_cases hmem : i ∈ Finset.Ico (0 : ℤ) (n : ℤ)
    · have hb := Finset.mem_Ico.mp hmem
      have h2 : i ∈ Finset.Ico (0 : ℤ) ((n + 1 : ℕ) : ℤ) :=
        Finset.mem_Ico.mpr ⟨hb.1, by omega⟩
      rw [if_pos hmem, if_neg (Ne.symm hi), if_pos h2, if_neg hi, add_zero]
    · have hb : ¬ ((0 : ℤ) ≤ i ∧ i < (n : ℤ)) := fun hc => hmem (Finset.mem_Ico.mpr hc)
      have h2 : i ∉ Finset.Ico (0 : ℤ) ((n + 1 : ℕ) : ℤ) := fun hc =>
        absurd (Finset.mem_Ico.mp hc) (by omega)
      rw [if_neg hmem, if_neg (Ne.symm hi), if_neg h2, add_zero]

/-! ## 6.  Existential projection

Freeing the last coordinate of an arity-`(n+1)` relation and then imposing the
smaller window is exactly `x ↦ ∃ y, R (x, y)`: the freed coordinate is the one
quantified away, and the window forces it back to zero in the result.

**These are quantifiers, not scratch space.**  `existsLast` and `existsAt` both
re-impose a window immediately, so the coordinate they free is bound and then
zeroed and there is no room left over.  A construction that needs *auxiliary*
coordinates lying outside the window cannot be obtained from them --- and such
constructions are not exotic: `Higman.HigmanAtoms` builds equality of two
coordinates by joining two successor legs at a position beyond both endpoints,
and the successor relation between two coordinates by copying a link above the
window.  Anything of that shape has to be carried out at the level of positions,
with every unnamed coordinate left free, and met with `windowSupport` only at
the very end.  The operations in this section are for binding a variable the
relation already has, not for acquiring one. -/

/-- **`∃` over the last variable.** -/
noncomputable def existsLast (n : ℕ) (R : Set E) : Set E :=
  freeAt n R ∩ windowSupport n

theorem isArity_existsLast (n : ℕ) (R : Set E) : IsArity n (existsLast n R) := by
  intro _ hf
  exact hf.2

theorem higmanGenerated_existsLast (n : ℕ) {R : Set E} (h : HigmanGenerated R) :
    HigmanGenerated (existsLast n R) := by
  unfold existsLast
  exact HigmanGenerated.inter (higmanGenerated_freeAt n h)
    (higmanGenerated_windowSupport n)

/-- **What the projection says.**  No hypothesis on `R` is needed: the window on
the left already forces the `n`-th coordinate of a member to vanish, so the
witness is recovered by adding the missing value back. -/
theorem mem_existsLast_iff (n : ℕ) (R : Set E) (f : E) :
    f ∈ existsLast n R ↔
      f ∈ windowSupport n ∧ ∃ y : ℤ, f + Finsupp.single (n : ℤ) y ∈ R := by
  unfold existsLast
  constructor
  · rintro ⟨hfree, hwin⟩
    obtain ⟨g, hg, hfg⟩ := (mem_freeAt_iff n R f).mp hfree
    have hfn : f (n : ℤ) = 0 :=
      ((mem_windowSupport_iff n f).mp hwin).2 (n : ℤ) le_rfl
    refine ⟨hwin, g (n : ℤ), ?_⟩
    have hEq : f + Finsupp.single (n : ℤ) (g (n : ℤ)) = g := by
      refine Finsupp.ext fun i => ?_
      rw [Finsupp.add_apply, Finsupp.single_apply]
      by_cases hi : (n : ℤ) = i
      · rw [if_pos hi]
        subst hi
        rw [hfn, zero_add]
      · rw [if_neg hi, add_zero]
        exact hfg i (Ne.symm hi)
    rw [hEq]
    exact hg
  · rintro ⟨hwin, y, hy⟩
    refine ⟨(mem_freeAt_iff n R f).mpr
      ⟨f + Finsupp.single (n : ℤ) y, hy, fun i hi => ?_⟩, hwin⟩
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hi), add_zero]

/-- The projection, read on tuples. -/
theorem winSeq_mem_existsLast_iff (n : ℕ) (R : Set E) (x : ℤ → ℤ) :
    winSeq n x ∈ existsLast n R ↔
      ∃ y : ℤ, winSeq (n + 1) (fun i => if i = (n : ℤ) then y else x i) ∈ R := by
  rw [mem_existsLast_iff]
  constructor
  · rintro ⟨_, y, hy⟩
    rw [winSeq_add_single] at hy
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨winSeq_mem_windowSupport n x, y, ?_⟩
    rw [winSeq_add_single]
    exact hy

/-- **`∃` over a coordinate that is not the last one, without a transposition.**
Free the coordinate, pin it to zero, and keep the window: the quantified
variable becomes a hole at `k` rather than being compacted away.  Compacting ---
shifting the coordinates above `k` down by one --- is what would need `τ`, and
this avoids it, at the price of leaving the arity at `n` rather than `n - 1`. -/
noncomputable def existsAt (k n : ℕ) (R : Set E) : Set E :=
  freeAt k R ∩ pinAt (k : ℤ) 0 ∩ windowSupport n

theorem isArity_existsAt (k n : ℕ) (R : Set E) : IsArity n (existsAt k n R) := by
  intro _ hf
  exact hf.2

theorem higmanGenerated_existsAt (k n : ℕ) {R : Set E} (h : HigmanGenerated R) :
    HigmanGenerated (existsAt k n R) := by
  unfold existsAt
  exact HigmanGenerated.inter
    (HigmanGenerated.inter (higmanGenerated_freeAt k h)
      (higmanGenerated_pinAt (k : ℤ) 0))
    (higmanGenerated_windowSupport n)

theorem mem_existsAt_iff (k n : ℕ) (R : Set E) (f : E) :
    f ∈ existsAt k n R ↔
      f ∈ windowSupport n ∧ f (k : ℤ) = 0 ∧
        ∃ y : ℤ, f + Finsupp.single (k : ℤ) y ∈ R := by
  unfold existsAt
  constructor
  · rintro ⟨⟨hfree, hpin⟩, hwin⟩
    have hfk : f (k : ℤ) = 0 := hpin
    obtain ⟨g, hg, hfg⟩ := (mem_freeAt_iff k R f).mp hfree
    refine ⟨hwin, hfk, g (k : ℤ), ?_⟩
    have hEq : f + Finsupp.single (k : ℤ) (g (k : ℤ)) = g := by
      refine Finsupp.ext fun i => ?_
      rw [Finsupp.add_apply, Finsupp.single_apply]
      by_cases hi : (k : ℤ) = i
      · rw [if_pos hi]
        subst hi
        rw [hfk, zero_add]
      · rw [if_neg hi, add_zero]
        exact hfg i (Ne.symm hi)
    rw [hEq]
    exact hg
  · rintro ⟨hwin, hfk, y, hy⟩
    refine ⟨⟨(mem_freeAt_iff k R f).mpr
      ⟨f + Finsupp.single (k : ℤ) y, hy, fun i hi => ?_⟩, hfk⟩, hwin⟩
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hi), add_zero]

/-! ## 7.  Padding

The same set with a wider window: the freed coordinate becomes a new variable on
which nothing is required. -/

/-- **A dummy last variable.** -/
noncomputable def padLast (n : ℕ) (R : Set E) : Set E :=
  freeAt n R ∩ windowSupport (n + 1)

theorem isArity_padLast (n : ℕ) (R : Set E) : IsArity (n + 1) (padLast n R) := by
  intro _ hf
  exact hf.2

theorem higmanGenerated_padLast (n : ℕ) {R : Set E} (h : HigmanGenerated R) :
    HigmanGenerated (padLast n R) := by
  unfold padLast
  exact HigmanGenerated.inter (higmanGenerated_freeAt n h)
    (higmanGenerated_windowSupport (n + 1))

/-- **What the padding says.**  Here the hypothesis on `R` is needed: it is what
makes the `n`-th coordinate of the recovered witness vanish, so that the value
written at `n` is unconstrained rather than merely shifted. -/
theorem mem_padLast_iff (n : ℕ) {R : Set E} (hR : IsArity n R) (f : E) :
    f ∈ padLast n R ↔
      f ∈ windowSupport (n + 1) ∧
        ∃ x ∈ R, f = x + Finsupp.single (n : ℤ) (f (n : ℤ)) := by
  unfold padLast
  constructor
  · rintro ⟨hfree, hwin⟩
    obtain ⟨g, hg, hfg⟩ := (mem_freeAt_iff n R f).mp hfree
    have hgn : g (n : ℤ) = 0 :=
      ((mem_windowSupport_iff n g).mp (hR hg)).2 (n : ℤ) le_rfl
    refine ⟨hwin, g, hg, ?_⟩
    refine Finsupp.ext fun i => ?_
    rw [Finsupp.add_apply, Finsupp.single_apply]
    by_cases hi : (n : ℤ) = i
    · rw [if_pos hi]
      subst hi
      rw [hgn, zero_add]
    · rw [if_neg hi, add_zero]
      exact hfg i (Ne.symm hi)
  · rintro ⟨hwin, x, hx, hfx⟩
    refine ⟨(mem_freeAt_iff n R f).mpr ⟨x, hx, fun i hi => ?_⟩, hwin⟩
    rw [hfx, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hi), add_zero]

/-- The padding, read on tuples: the new coordinate is genuinely free. -/
theorem winSeq_mem_padLast_iff (n : ℕ) {R : Set E} (hR : IsArity n R) (x : ℤ → ℤ)
    (y : ℤ) :
    winSeq (n + 1) (fun i => if i = (n : ℤ) then y else x i) ∈ padLast n R
      ↔ winSeq n x ∈ R := by
  rw [← winSeq_add_single]
  unfold padLast
  constructor
  · rintro ⟨hfree, _⟩
    obtain ⟨g, hg, hfg⟩ :=
      (mem_freeAt_iff n R (winSeq n x + Finsupp.single (n : ℤ) y)).mp hfree
    have hgn : g (n : ℤ) = 0 :=
      ((mem_windowSupport_iff n g).mp (hR hg)).2 (n : ℤ) le_rfl
    have hxg : winSeq n x = g := by
      refine Finsupp.ext fun i => ?_
      by_cases hi : i = (n : ℤ)
      · have hnot : (n : ℤ) ∉ Finset.Ico (0 : ℤ) (n : ℤ) := by
          rw [Finset.mem_Ico]
          omega
        rw [hi, hgn, winSeq_apply, if_neg hnot]
      · have h1 := hfg i hi
        rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hi),
          add_zero] at h1
        exact h1
    rw [hxg]
    exact hg
  · intro hx
    refine ⟨(mem_freeAt_iff n R (winSeq n x + Finsupp.single (n : ℤ) y)).mpr
      ⟨winSeq n x, hx, fun i hi => ?_⟩, ?_⟩
    · rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hi), add_zero]
    · rw [winSeq_add_single]
      exact winSeq_mem_windowSupport (n + 1) (fun i => if i = (n : ℤ) then y else x i)

end Seq
end Higman
end GroupApproximation
