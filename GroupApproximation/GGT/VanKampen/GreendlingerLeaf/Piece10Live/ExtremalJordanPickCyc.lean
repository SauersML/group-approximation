import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCycOrbit
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCycFace
import GroupApproximation.Meta.AxiomGuard

/-!
# The orbit-count parity law, proved

Lane gl-p10-44.  Notation: `M = X.toCombMap`, `c = K.boundary.cycle` (a list without repeats, of
length `L`), `R = FaceClassStep M (walkKeep M c)`, `f = extremalJordanPickCountParity_perm K`
(`d ↦ α (σ_P d)` on `c`, the identity off `c`), and `O = extremalJordanPickCount_outside K`.

**Theorem** (`extremalJordanPickCyc_cycles`, which closes
`ExtremalJordanPickCountParityCyclesStatement`).  For a pocket face set `K` whose boundary is a
closed walk, `#O = L - #(supp f) + #(cycleType f)`.  In particular the two sides agree mod 2.
Only the closed-walk hypothesis is used; the other premises of the Statement are not needed.

**Proof.**
1. `O` is the image of `c` under `d ↦ [α d]` (`extremalJordanPickCyc_outside_eq`).  Being based
   in `K.faces` is constant on face classes off the walk.  By connectivity of `M`, each outside
   class contains a kept dart, which is based outside, hence is a reversed walk dart.
2. For `d, d' ∈ c`: `[α d] = [α d']` exactly when `SameCycle f d d'`.
   * (⇐) `extremalJordanPickCyc_class_of_sameCycle`: the rotation run from `α d` to `σ_P d`
     crosses only unkept darts, so it is a chain of face-class steps.
   * (⇒) `extremalJordanPickCyc_sameCycle_of_class`: the separation theorem for the connected
     walk map `P` puts `α d`, `α d'` on one face of `P`, and on reversed walk darts the face
     permutation of `P` is conjugate to `f`.
3. `supp f ⊆ c`, since `f` fixes every dart off `c`.  The orbit count
   `extremalJordanPickCyc_card_image` then gives `#O + #(supp f) = L + #(cycleType f)`.  As
   `#(supp f) ≤ L`, this is the claimed identity.

The parity half `ExtremalJordanPickCountParityStatement` then follows from the existing
reduction `extremalJordanPickCountParity_parity` (`extremalJordanPickCyc_parity`).

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open scoped Classical

section CycEnd

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- The face permutation moves only walk darts. -/
theorem extremalJordanPickCyc_support_subset (K : PocketFaceSet D eps X lo hi) :
    (extremalJordanPickCountParity_perm K).support ⊆ K.boundary.cycle.toFinset := by
  intro d hd
  rw [List.mem_toFinset]
  by_contra hc
  exact Equiv.Perm.mem_support.mp hd (extremalJordanPickCountParity_perm_of_not_mem K d hc)

/-- **Claim 2**: two reversed walk darts share a face class exactly when the walk darts lie in
one cycle of the face permutation. -/
theorem extremalJordanPickCyc_class_iff (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk) :
    ∀ x ∈ K.boundary.cycle.toFinset, ∀ y ∈ K.boundary.cycle.toFinset,
      (Quot.mk (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle))
          (X.toCombMap.alpha x) =
        Quot.mk (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle))
          (X.toCombMap.alpha y) ↔
        (extremalJordanPickCountParity_perm K).SameCycle x y) := by
  intro x hx y hy
  rw [List.mem_toFinset] at hx hy
  constructor
  · intro hq
    exact extremalJordanPickCyc_sameCycle_of_class K hK hx hy (Quot.eqvGen_exact hq)
  · intro hc
    exact Quot.eqvGen_sound (extremalJordanPickCyc_class_of_sameCycle K hx hc)

/-- **The orbit-count law for one pocket face set** (exact form, closed walk only). -/
theorem extremalJordanPickCyc_card_outside (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) :
    (extremalJordanPickCount_outside K).card + (extremalJordanPickCountParity_perm K).support.card
      = K.boundary.cycle.length + (extremalJordanPickCountParity_perm K).cycleType.card := by
  have h := extremalJordanPickCyc_card_image (extremalJordanPickCountParity_perm K)
    K.boundary.cycle.toFinset (fun d =>
      Quot.mk (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle))
        (X.toCombMap.alpha d))
    (extremalJordanPickCyc_support_subset K) (extremalJordanPickCyc_class_iff K hK)
  rw [List.toFinset_card_of_nodup K.boundary.cycle_nodup] at h
  rw [extremalJordanPickCyc_outside_eq K]
  exact h

/-- **The orbit-count parity law for one pocket face set.** -/
theorem extremalJordanPickCyc_of_pocket (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk) :
    ExtremalJordanPickCountParityCycles K := by
  have h := extremalJordanPickCyc_card_outside K hK
  have hle := Finset.card_le_card (extremalJordanPickCyc_support_subset K)
  rw [List.toFinset_card_of_nodup K.boundary.cycle_nodup] at hle
  unfold ExtremalJordanPickCountParityCycles
  omega

end CycEnd

/-- **`ExtremalJordanPickCountParityCyclesStatement`, proved.** -/
theorem extremalJordanPickCyc_cycles : ExtremalJordanPickCountParityCyclesStatement.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ K hK _ _ _ _ _ _ _
  exact extremalJordanPickCyc_of_pocket K hK

/-- **`ExtremalJordanPickCountParityStatement` (the parity half), proved.** -/
theorem extremalJordanPickCyc_parity : ExtremalJordanPickCountParityStatement.{u, w, v} :=
  extremalJordanPickCountParity_parity extremalJordanPickCyc_cycles

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_support_subset
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_class_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_card_outside
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_of_pocket
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_cycles
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_parity
