import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchLobeProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchFan
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchOffFace
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-56: the walk turn is a fan, and the first entry step

Lane gl-p07-56.  The target is `FourPieceWitness.WitnessStepPinchLobeStatement`
(`WitnessStepPinchLobeStatement.lean`, lane gl-p07-55).  It is NOT closed.  This lane proves two
pieces of it and states the residual `FourPieceWitness.WitnessStepPinchParityStatement`
(`WitnessStepPinchParityStatement.lean`).  `WitnessStepPinchParityProof.lean` proves the target
from the residual, proves the converse, and wires the residual through to `PinchOff`, `Pinch` and
`WitnessStepSkip`.  Certifies no printed sentence on its own.  NOT COMPILED.

## Notation

`w = witnessSublistCurve a b G₁ G₂`, `l = invDarts X ow` (the list `ow.reverse.map α`), and
`F = witnessFaces a b K c`.  `keep z` is `walkKeep ow z`, that is, `z ∈ ow ∨ α z ∈ ow`.

## Piece 1: the walk turn is a fan (`witnessStepPinchParity_turn_fan`), pure CombMap

Let `(x, y)` be consecutive in a rotation of `l`.  Then the walk `ow` has `α y` followed by `α x`.
Let `m` be the first index with `keep (σ^m y)` (`PocketRun.exists_firstKeep`, using `α (α y) = y`).
Then `σ^m y = α x` (`witnessStepSide_sigma_of_rotate`).

*Claim.* For `0 < k < m`, both `faceOf (σ^k y)` and `faceOf (α (σ^k y))` are off `F`.

*Proof.* Recall `facePerm = σ ∘ α`.  So `σ z = facePerm (α z)`, and `faceOf (σ z) = faceOf (α z)`
(`witnessStepPinchParity_faceOf_sigma`).  Induct on `k`.
* `k = 1`: `faceOf (σ y) = faceOf (α y)`.  This is off `F` by `mem_iff`, since `α y ∈ ow`.
* `k + 1` with `k ≥ 1`: `faceOf (σ^(k+1) y) = faceOf (α (σ^k y))`.  The dart `σ^k y` is not kept,
  so it is off `ow`.  Its face is off `F` (induction).  By `mem_iff`, a dart that is off `ow` and
  has face off `F` has `α`-face off `F` (`witnessStepPinchOff_alpha_faceOf_not_mem`).
The second component is the same `mem_iff` step at `k`.  ∎

So `WitnessStepPinchFan F y (α x)`: the sector of the walk turn at the vertex of `y` meets no face
of `F`.  This uses `mem_iff` only, not the noncrossing of `l`.

## Piece 2: the first entry step (`witnessStepPinchParity_entry`), pure lists

If a list `L` has one member in `S` and another member not in `S`, then some rotation of `L` is
`s ++ x' :: y' :: t` with `x' ∉ S` and `y' ∈ S`.  *Proof.* Split `L = u ++ b :: v` at the member
`b ∉ S`.  Rotating by `u.length` gives `b :: (v ++ u)`.  In a list headed by a non-member of `S`
that contains a member, induct on the tail: the first member of `S` has a non-member just before
it (`witnessStepPinchParity_entry_linear`).  ∎

## Route of the reduction (`WitnessStepPinchParityProof.lean`)

Take a pinch `(x, y)` with `w = pre ++ y :: (mid ++ x :: post)` and an open `e ∈ pre` with `e ∈ l`.
We derive `False`.
* `y ∈ l` (from the rotation), and `y ∉ pre`, since `w` has no duplicates
  (`witnessSublist_curve_nodup`, `witnessStepPinchParity_not_mem_pre`).
* Piece 2 with `S = pre`, `L = l` gives an **entry step** `(x', y')` of `l` with `x' ∉ pre` and
  `y' ∈ pre`.
* Piece 1 gives `WitnessStepPinchFan F y' (α x')`.  `hnb` gives `faceOf y' ∈ F`
  (`witnessStepPinchParity_face_of_rotate`).
* The residual says that such an entry step does not exist.

Converse (`witnessStepPinchParity_parity_of_pinchLobe`): if an entry step exists, then `y' ∈ pre`
lies in `l` and is open (its face is in `F`).  This contradicts the target.  So target and
residual are **logically equivalent**, and both directions are proved.

## Truth check (Python, `SP/gl-p07-56/parity_model.py`, scratchpad, not built)

These are the planar flowers of `SP/gl-p07-55`, with `k ≤ 3`, every cut mask, every start face
and every linearisation.
| k | turns checked (W) | pinches with `y` before `x` | entry candidates checked (E) |
|---|-------------------|-----------------------------|------------------------------|
| 1 | 29                | 8                           | 24                           |
| 2 | 749               | 636                         | 2692                         |
| 3 | 13151             | 15486                       | 86242                        |
* (W) Piece 1 holds at every turn of `l`.
* (E) No entry step exists at any pinch with `y` before `x`, so the residual holds.  The pinch
  counts match the gl-p07-55 table.
* (I) The discrete intermediate value lemma was checked on 20000 random lists.

## LOUD: equal in logical strength, strictly smaller in proof content

The residual is **equivalent** to the target, and both directions are proved.  It is NOT strictly
weaker.  No true strictly weaker gap exists for a proved reduction: any `G` with `G → target`
that the target implies is equivalent to it.  A pure CombMap form without witness data is not
available.  The order-free abstraction is FALSE: the four-petal model (gl-p07-54 notes) has a
crossing `Γ`, and a pure lemma would need `Γ` noncrossing, which the repo does not prove.

What the reduction discharges:
* the global quantifier over `e ∈ pre`.  It becomes a single turn `(x', y')` of the walk, where
  `l` passes from outside `pre` into `pre`;
* the local geometry at that turn.  The sector from `y'` to `α x'` at the vertex of `y'` is
  F-free (Piece 1), and `faceOf y' ∈ F`.

## What is left: no entry step into `pre`

At an off-lobe pinch with `y` before `x`, no consecutive `(x', y')` of `l` has `x' ∉ pre`, `y' ∈ pre`.
Paper route: `α y'` is a loop-A dart of `Γ` on `ow`, and `α x'` is not on the `pre` part of
loop A.  The walk turn at the vertex `u` of `y'` is an F-free sector.  So `u` is a common vertex of
loop A and the rest of `Γ`, and at `u` the walk leaves loop A.  Ruling this out is the Jordan
separation of the two lobes, which needs `Γ` noncrossing.  The repo does not prove it.  A ZMod 2
telescoping, in the style of gl-p10-25, counts crossings of a dual path with `l`.  It does not
decide on which lobe a face lies without knowing `ow`, so it does not close this gap.

## Notes

* **Backward disjunct kept**, as in the target.
* **Premise block kept whole.**  No context-free Jordan statement.
* **AVOID list respected.**  No `RigidPolar*`, `KerNormallyGenerated`, `PocketFourPiece*`,
  `FrameConeFourStatement` or `ExtremalEndBlockStatement`.  No surgery, and no loose-count or
  minimal-count descent.  The entry step is an existence statement from the discrete intermediate
  value theorem, with no count or measure.  The backward disjunct is not used as the covering case.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Linear entry step.**  A list headed by a non-member of `S` that contains a member of `S` has
a non-member of `S` right before a member of `S`. -/
theorem witnessStepPinchParity_entry_linear {β : Type*} (S : List β) :
    ∀ (b : β) (L : List β), b ∉ S → (∃ e ∈ L, e ∈ S) →
      ∃ (s : List β) (x y : β) (t : List β), b :: L = s ++ x :: y :: t ∧ x ∉ S ∧ y ∈ S
  | _, [], _, ⟨_, he, _⟩ => by simp at he
  | b, c :: L, hb, ⟨e, he, heS⟩ => by
    by_cases hc : c ∈ S
    · exact ⟨[], b, c, L, rfl, hb, hc⟩
    · have hL : ∃ e ∈ L, e ∈ S := by
        rcases List.mem_cons.mp he with rfl | he'
        · exact absurd heS hc
        · exact ⟨e, he', heS⟩
      obtain ⟨s, x, y, t, hst, hx, hy⟩ := witnessStepPinchParity_entry_linear S c L hc hL
      exact ⟨b :: s, x, y, t, by rw [hst, List.cons_append], hx, hy⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchParity_entry_linear

/-- **Cyclic entry step (discrete intermediate value).**  A list with a member in `S` and a member
not in `S` has a rotation `s ++ x :: y :: t` with `x ∉ S` and `y ∈ S`. -/
theorem witnessStepPinchParity_entry {β : Type*} {S L : List β} {e b : β}
    (he : e ∈ L) (heS : e ∈ S) (hb : b ∈ L) (hbS : b ∉ S) :
    ∃ (n : ℕ) (s : List β) (x y : β) (t : List β),
      L.rotate n = s ++ x :: y :: t ∧ x ∉ S ∧ y ∈ S := by
  obtain ⟨u, v, rfl⟩ := List.append_of_mem hb
  have he' : ∃ e' ∈ v ++ u, e' ∈ S := by
    refine ⟨e, ?_, heS⟩
    rcases List.mem_append.mp he with h | h
    · exact List.mem_append_right _ h
    · rcases List.mem_cons.mp h with rfl | h
      · exact absurd heS hbS
      · exact List.mem_append_left _ h
  obtain ⟨s, x, y, t, hst, hx, hy⟩ := witnessStepPinchParity_entry_linear S b (v ++ u) hbS he'
  refine ⟨u.length, s, x, y, t, ?_, hx, hy⟩
  rw [List.rotate_append_length_eq, List.cons_append]
  exact hst

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchParity_entry

/-- The second entry of a rotation window is a member of the list. -/
theorem witnessStepPinchParity_mem_of_rotate {β : Type*} {L s t : List β} {n : ℕ} {x y : β}
    (h : L.rotate n = s ++ x :: y :: t) : y ∈ L :=
  List.mem_rotate.mp (by rw [h]; simp)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchParity_mem_of_rotate

/-- In a list without duplicates, `y` is not in the prefix before it. -/
theorem witnessStepPinchParity_not_mem_pre {β : Type*} {L pre mid post : List β} {x y : β}
    (hL : L.Nodup) (h : L = pre ++ y :: (mid ++ x :: post)) : y ∉ pre := by
  intro hy
  rw [h] at hL
  exact (List.nodup_append.mp hL).2.2 y hy y (by simp) rfl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchParity_not_mem_pre

/-- **`faceOf (σ z) = faceOf (α z)`**, as `σ z = facePerm (α z)`. -/
theorem witnessStepPinchParity_faceOf_sigma {M : CombMap.{v}} (z : M.Dart) :
    M.faceOf (M.sigma z) = M.faceOf (M.alpha z) := by
  have h1 : M.facePerm (M.alpha z) = M.sigma z := by
    rw [PocketRun.facePerm_eq_sigma_alpha, M.alpha_involutive z]
  rw [← h1]
  exact M.faceOf_facePerm _

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchParity_faceOf_sigma

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
