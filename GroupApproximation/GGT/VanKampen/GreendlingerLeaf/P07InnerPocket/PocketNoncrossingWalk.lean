import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossingClass
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: the pocket orbit is a noncrossing closed walk

Lane `gl-p07-05`, second module.  Infrastructure for
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`, Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b).  Certifies no printed sentence on its own.

## The orbit (lane `gl-p07-04` output, as hypotheses)

`PocketOrbit M keep c L` collects the properties of the face orbit `L` of the pocket class that
lane 04 produces: `L` is a nonempty duplicate-free closed vertex chain, its darts are exactly the
retained darts based in the class of `c`, and the first return of the rotation from `alpha d`
onto a retained edge is again in `L`.  Lane 04 also asks that this return is the successor of `d`;
that clause is not needed here, so `PocketOrbit` is implied by lane 04's orbit.

## The proof

* `alpha_not_mem`: `d ∈ L` and `alpha d ∈ L` would give a retained edge with both sides in the
  class, against the no-bridge hypothesis.
* `turn_mem`: every edge of `L` is retained.  Let `m` be the first return onto an edge of `L` and
  `m₀ ≤ m` the first return onto a retained edge (`Nat.find`).  The orbit hypothesis puts
  `σ^m₀ (α d)` in `L`, so `m₀ = m` by minimality of `m`.
* `sideFaces L = class` (`sideFaces_eq_faceClass`).
  * `⊆`: along a class of `walkKeep L`, "the face is in the class" is invariant.  Face moves keep
    the face.  An edge off `L` that is retained has neither dart in `L`, so neither side in the
    class (membership clause).  An edge that is not retained keeps the class by closure.
  * `⊇`: fewer retained darts give larger classes, and any dart of `L ≠ []` is based in the class.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u

open Equiv SimpleClosedWalkSides Surgery.MapCollapse

namespace PocketNoncrossing

/-- **The pocket face orbit**, as delivered by lane `gl-p07-04` (without its successor clause). -/
structure PocketOrbit (M : CombMap.{u}) (keep : M.Dart → Prop) (c : M.Face) (L : List M.Dart) :
    Prop where
  ne_nil : L ≠ []
  nodup : L.Nodup
  chain : L.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e
  closes : M.vertexOf (M.alpha (L.getLast ne_nil)) = M.vertexOf (L.head ne_nil)
  mem_iff : ∀ d, d ∈ L ↔ keep d ∧ M.faceOf d ∈ faceClass M keep c
  turn : ∀ d ∈ L, ∀ m : ℕ, 0 < m → keep ((M.sigma ^ m) (M.alpha d)) →
    (∀ k, 0 < k → k < m → ¬ keep ((M.sigma ^ k) (M.alpha d))) → (M.sigma ^ m) (M.alpha d) ∈ L

variable {M : CombMap.{u}} {keep : M.Dart → Prop} {c : M.Face} {L : List M.Dart}

/-- The edges of the orbit are retained. -/
theorem keep_of_walkKeep (hα : ∀ d, keep (M.alpha d) ↔ keep d)
    (hmem : ∀ d, d ∈ L ↔ keep d ∧ M.faceOf d ∈ faceClass M keep c) :
    ∀ x, walkKeep M L x → keep x := by
  rintro x (hx | hx)
  · exact ((hmem x).mp hx).1
  · exact (hα x).mp ((hmem _).mp hx).1

/-- **The side of the orbit is the class.** -/
theorem sideFaces_eq_faceClass (hα : ∀ d, keep (M.alpha d) ↔ keep d) (hne : L ≠ [])
    (hmem : ∀ d, d ∈ L ↔ keep d ∧ M.faceOf d ∈ faceClass M keep c) :
    sideFaces M L = faceClass M keep c := by
  have halpha : ∀ x, ¬ walkKeep M L x →
      (M.faceOf (M.alpha x) ∈ faceClass M keep c ↔ M.faceOf x ∈ faceClass M keep c) := by
    intro x hx
    have hxL : x ∉ L := fun h => hx (Or.inl h)
    have haL : M.alpha x ∉ L := fun h => hx (Or.inr h)
    by_cases hk : keep x
    · have h₁ : M.faceOf x ∉ faceClass M keep c := fun h => hxL ((hmem x).mpr ⟨hk, h⟩)
      have h₂ : M.faceOf (M.alpha x) ∉ faceClass M keep c :=
        fun h => haL ((hmem _).mpr ⟨(hα x).mpr hk, h⟩)
      exact ⟨fun h => (h₂ h).elim, fun h => (h₁ h).elim⟩
    · constructor
      · intro h
        have h' := faceOf_alpha_mem_faceClass M keep c (fun hk' => hk ((hα x).mp hk')) h
        rw [M.alpha_involutive x] at h'
        exact h'
      · exact faceOf_alpha_mem_faceClass M keep c hk
  ext f
  obtain ⟨z, hz⟩ := Quotient.exists_rep f
  have hz' : M.faceOf z = f := hz
  subst hz'
  rw [mem_sideFaces_iff]
  constructor
  · rintro ⟨d, hd, h⟩
    have hinv : M.faceOf d ∈ faceClass M keep c ↔ M.faceOf z ∈ faceClass M keep c :=
      invariant_of_eqvGen M (fun x => M.faceOf x ∈ faceClass M keep c)
        (fun x => by
          show M.faceOf (M.facePerm x) ∈ faceClass M keep c ↔ M.faceOf x ∈ faceClass M keep c
          rw [M.faceOf_facePerm]) halpha h
    exact hinv.mp ((hmem d).mp hd).2
  · intro hS
    obtain ⟨y, hy, hyz⟩ := (faceOf_mem_faceClass_iff M keep c z).mp hS
    obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil L hne
    obtain ⟨y', hy', hy'd⟩ := (faceOf_mem_faceClass_iff M keep c d).mp ((hmem d).mp hd).2
    have hyy : Relation.EqvGen (CombMap.FaceClassStep M keep) y' y :=
      eqvGen_faceClass_of_sameCycle M keep ((M.faceOf_eq_iff y' y).mp (hy'.trans hy.symm))
    refine ⟨d, hd, faceClass_mono M (keep := keep) (keep' := walkKeep M L)
      (fun x hx hw => hx (keep_of_walkKeep hα hmem x hw)) ?_⟩
    exact .trans _ _ _ (.symm _ _ hy'd) (.trans _ _ _ hyy hyz)

/-- **The turning condition** from the first return onto retained edges. -/
theorem turn_mem_of_orbit (hα : ∀ d, keep (M.alpha d) ↔ keep d)
    (hmem : ∀ d, d ∈ L ↔ keep d ∧ M.faceOf d ∈ faceClass M keep c)
    (hret : ∀ d ∈ L, ∀ m : ℕ, 0 < m → keep ((M.sigma ^ m) (M.alpha d)) →
      (∀ k, 0 < k → k < m → ¬ keep ((M.sigma ^ k) (M.alpha d))) →
      (M.sigma ^ m) (M.alpha d) ∈ L) :
    ∀ d ∈ L, ∀ m : ℕ, 0 < m → walkKeep M L ((M.sigma ^ m) (M.alpha d)) →
      (∀ k, 0 < k → k < m → ¬ walkKeep M L ((M.sigma ^ k) (M.alpha d))) →
      (M.sigma ^ m) (M.alpha d) ∈ L := by
  classical
  intro d hd m hm hkeep havoid
  have hkm : keep ((M.sigma ^ m) (M.alpha d)) := keep_of_walkKeep hα hmem _ hkeep
  have hex : ∃ n : ℕ, 0 < n ∧ keep ((M.sigma ^ n) (M.alpha d)) := ⟨m, hm, hkm⟩
  have hspec : 0 < Nat.find hex ∧ keep ((M.sigma ^ Nat.find hex) (M.alpha d)) :=
    Nat.find_spec hex
  have hle : Nat.find hex ≤ m := Nat.find_min' hex ⟨hm, hkm⟩
  have hmin : ∀ k, 0 < k → k < Nat.find hex → ¬ keep ((M.sigma ^ k) (M.alpha d)) :=
    fun k hk hlt hkk => Nat.find_min hex hlt ⟨hk, hkk⟩
  have hin : (M.sigma ^ Nat.find hex) (M.alpha d) ∈ L :=
    hret d hd (Nat.find hex) hspec.1 hspec.2 hmin
  by_cases hlt : Nat.find hex < m
  · exact (havoid _ hspec.1 hlt (Or.inl hin)).elim
  · have heq : Nat.find hex = m := by omega
    rw [heq] at hin
    exact hin

/-- **The pocket orbit is a noncrossing closed walk**, given that no retained edge is a bridge of
the class. -/
theorem isNoncrossingClosedWalk_of_orbit (hα : ∀ d, keep (M.alpha d) ↔ keep d)
    (hL : PocketOrbit M keep c L)
    (hbridge : ∀ d, keep d →
      ¬ (M.faceOf d ∈ faceClass M keep c ∧ M.faceOf (M.alpha d) ∈ faceClass M keep c)) :
    IsNoncrossingClosedWalk M L where
  ne_nil := hL.ne_nil
  nodup := hL.nodup
  chain := hL.chain
  closes := hL.closes
  alpha_not_mem := by
    intro d hd ha
    obtain ⟨hk, hS⟩ := (hL.mem_iff d).mp hd
    exact hbridge d hk ⟨hS, ((hL.mem_iff _).mp ha).2⟩
  turn_mem := turn_mem_of_orbit hα hL.mem_iff hL.turn

end PocketNoncrossing

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossing.keep_of_walkKeep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossing.sideFaces_eq_faceClass
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossing.turn_mem_of_orbit
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossing.isNoncrossingClosedWalk_of_orbit
