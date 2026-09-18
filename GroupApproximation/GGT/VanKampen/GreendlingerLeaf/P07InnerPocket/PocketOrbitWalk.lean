import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbitClass
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossingWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: the face orbit of the pocket class

Lane `gl-p07-04`, second module.  Infrastructure for
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement` (`P07LakeExclusion/InnerTwoArcLong.lean`),
Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Certifies no printed sentence on its own.

## Statement

`M` planar, `keep` an `alpha`-closed dart predicate with some kept dart, `N = keepMap M keep`
connected, `c` a face of `M`.  Then there is a list `L` of darts that is a nonempty duplicate-free
closed vertex chain, whose darts are exactly the kept darts based in `faceClass M keep c`, and such
that for `d = L[i]`, the first `m > 0` with `σ^m (α d)` kept gives `σ^m (α d) = L[i+1 mod |L|]`
(`exists_pocketOrbit_of_connected`, packaged with lane 05's `PocketNoncrossing.PocketOrbit`).

## The proof

`L = keepWalk x₀`, the orbit of a kept dart `x₀` based in the class (`exists_keep_mem_faceClass`)
under the face permutation `P` of `N`, read in `M` (`LakeFill.orbitMap`), exactly as for
`LakeFill.lakeWalk`.
* chain and closing: `vertexOf (α x) = vertexOf (P x)` (`vertexOf_keepMap_facePerm`);
* membership: `P` keeps the class, and the class lies in one face of `N` (`keepMap_faceOf_eq`);
* successor: `P x = σ^m (α x)` for the first kept return `m` (`keepMap_turn`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u

open Equiv SimpleClosedWalkSides PocketNoncrossing
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill

namespace PocketOrbit

/-- **The face orbit of a kept dart**, read in the ambient map. -/
noncomputable def keepWalk (M : CombMap.{u}) (keep : M.Dart → Prop)
    (hkeep : ∀ d, keep (M.alpha d) ↔ keep d) (x₀ : (keepMap M keep hkeep).Dart) :
    List M.Dart :=
  orbitMap (keepMap M keep hkeep).facePerm x₀ fun d : (keepMap M keep hkeep).Dart => d.1

section Walk

variable {M : CombMap.{u}} {keep : M.Dart → Prop} (hkeep : ∀ d, keep (M.alpha d) ↔ keep d)

theorem length_keepWalk (x₀ : (keepMap M keep hkeep).Dart) :
    (keepWalk M keep hkeep x₀).length = period (keepMap M keep hkeep).facePerm x₀ :=
  length_orbitMap _ _ _

theorem getElem_keepWalk (x₀ : (keepMap M keep hkeep).Dart) (i : ℕ)
    (hi : i < (keepWalk M keep hkeep x₀).length) :
    (keepWalk M keep hkeep x₀)[i]'hi = (((keepMap M keep hkeep).facePerm ^ i) x₀).1 :=
  getElem_orbitMap _ _ _ i hi

theorem keepWalk_getElem_succ_mod (x₀ : (keepMap M keep hkeep).Dart) (i : ℕ)
    (hi : i < (keepWalk M keep hkeep x₀).length) :
    (keepWalk M keep hkeep x₀)[(i + 1) % (keepWalk M keep hkeep x₀).length]'
        (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)) =
      ((keepMap M keep hkeep).facePerm (((keepMap M keep hkeep).facePerm ^ i) x₀)).1 :=
  orbitMap_getElem_succ_mod _ _ _ i hi

theorem keepWalk_ne_nil (x₀ : (keepMap M keep hkeep).Dart) : keepWalk M keep hkeep x₀ ≠ [] :=
  List.ne_nil_of_length_pos (by
    rw [length_keepWalk]
    exact (period_spec _ _).1)

theorem keepWalk_nodup (x₀ : (keepMap M keep hkeep).Dart) : (keepWalk M keep hkeep x₀).Nodup :=
  nodup_orbitMap (keepMap M keep hkeep).facePerm x₀
    (f := fun d : (keepMap M keep hkeep).Dart => d.1) (fun _ _ h => Subtype.ext h)

theorem keepWalk_step (x₀ : (keepMap M keep hkeep).Dart) (n : ℕ) :
    M.vertexOf (M.alpha (((keepMap M keep hkeep).facePerm ^ n) x₀).1) =
      M.vertexOf (((keepMap M keep hkeep).facePerm ^ (n + 1)) x₀).1 := by
  rw [pow_succ', Equiv.Perm.mul_apply]
  exact vertexOf_keepMap_facePerm hkeep _

theorem keepWalk_chain (x₀ : (keepMap M keep hkeep).Dart) :
    (keepWalk M keep hkeep x₀).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e :=
  orbitMap_isChain (keepMap M keep hkeep).facePerm x₀ (fun d : (keepMap M keep hkeep).Dart => d.1)
    (R := fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) (keepWalk_step hkeep x₀)

theorem keepWalk_closes (x₀ : (keepMap M keep hkeep).Dart) (hne : keepWalk M keep hkeep x₀ ≠ []) :
    M.vertexOf (M.alpha ((keepWalk M keep hkeep x₀).getLast hne)) =
      M.vertexOf ((keepWalk M keep hkeep x₀).head hne) :=
  orbitMap_closes (keepMap M keep hkeep).facePerm x₀ (fun d : (keepMap M keep hkeep).Dart => d.1)
    (R := fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) (keepWalk_step hkeep x₀) hne

/-- **The darts of the orbit** are the kept darts based in the class. -/
theorem mem_keepWalk_iff (hM : M.IsPlanar) (hN : (keepMap M keep hkeep).IsConnected)
    {c : M.Face} {x₀ : (keepMap M keep hkeep).Dart} (hx₀ : M.faceOf x₀.1 ∈ faceClass M keep c)
    (d : M.Dart) :
    d ∈ keepWalk M keep hkeep x₀ ↔ keep d ∧ M.faceOf d ∈ faceClass M keep c := by
  unfold keepWalk
  rw [mem_orbitMap_iff]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨(((keepMap M keep hkeep).facePerm ^ n) x₀).2,
      keepMap_facePerm_pow_mem_faceClass hkeep hx₀ n⟩
  · rintro ⟨hd, hc⟩
    have hface := keepMap_faceOf_eq hkeep hM hN (x := x₀) (y := ⟨d, hd⟩) hx₀ hc
    obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq
      (((keepMap M keep hkeep).faceOf_eq_iff x₀ ⟨d, hd⟩).mp hface)
    exact ⟨n, congrArg (fun z : (keepMap M keep hkeep).Dart => z.1) hn⟩

/-- **Turn to the successor** on the orbit: the first kept return from `α L[i]` is `L[i+1]`. -/
theorem keepWalk_turn_next (x₀ : (keepMap M keep hkeep).Dart) (i : ℕ)
    (hi : i < (keepWalk M keep hkeep x₀).length) (m : ℕ) (hm : 0 < m)
    (hk : keep ((M.sigma ^ m) (M.alpha (keepWalk M keep hkeep x₀)[i])))
    (hfirst : ∀ k, 0 < k → k < m →
      ¬ keep ((M.sigma ^ k) (M.alpha (keepWalk M keep hkeep x₀)[i]))) :
    (M.sigma ^ m) (M.alpha (keepWalk M keep hkeep x₀)[i]) =
      (keepWalk M keep hkeep x₀)[(i + 1) % (keepWalk M keep hkeep x₀).length]'
        (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)) := by
  rw [keepWalk_getElem_succ_mod hkeep x₀ i hi]
  rw [getElem_keepWalk hkeep x₀ i hi] at hk hfirst ⊢
  obtain ⟨m₀, hm₀, hpm, havoid⟩ :=
    keepMap_facePerm_firstReturn hkeep (((keepMap M keep hkeep).facePerm ^ i) x₀)
  rw [hpm]
  rcases lt_trichotomy m m₀ with hlt | heq | hgt
  · exact absurd hk (havoid m hm hlt)
  · rw [heq]
  · refine absurd ?_ (hfirst m₀ hm₀ hgt)
    rw [← hpm]
    exact ((keepMap M keep hkeep).facePerm (((keepMap M keep hkeep).facePerm ^ i) x₀)).2

theorem keepWalk_turn_mem (x₀ : (keepMap M keep hkeep).Dart) :
    ∀ d ∈ keepWalk M keep hkeep x₀, ∀ m : ℕ, 0 < m → keep ((M.sigma ^ m) (M.alpha d)) →
      (∀ k, 0 < k → k < m → ¬ keep ((M.sigma ^ k) (M.alpha d))) →
      (M.sigma ^ m) (M.alpha d) ∈ keepWalk M keep hkeep x₀ := by
  intro d hd m hm hk hfirst
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  rw [keepWalk_turn_next hkeep x₀ i hi m hm hk hfirst]
  exact List.getElem_mem _

/-- **The pocket face orbit**, for a planar map whose kept map is connected. -/
theorem exists_pocketOrbit_of_connected (hM : M.IsPlanar) (hN : (keepMap M keep hkeep).IsConnected)
    {d₀ : M.Dart} (hd₀ : keep d₀) (c : M.Face) :
    ∃ L : List M.Dart, PocketNoncrossing.PocketOrbit M keep c L ∧
      ∀ (i : ℕ) (hi : i < L.length) (m : ℕ), 0 < m → keep ((M.sigma ^ m) (M.alpha L[i])) →
        (∀ k, 0 < k → k < m → ¬ keep ((M.sigma ^ k) (M.alpha L[i]))) →
        (M.sigma ^ m) (M.alpha L[i]) =
          L[(i + 1) % L.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)) := by
  obtain ⟨x, hx, hxc⟩ := exists_keep_mem_faceClass (M.connected_of_planar hM) hd₀ c
  have hx₀ : M.faceOf (⟨x, hx⟩ : (keepMap M keep hkeep).Dart).1 ∈ faceClass M keep c := hxc
  refine ⟨keepWalk M keep hkeep ⟨x, hx⟩,
    { ne_nil := keepWalk_ne_nil hkeep _
      nodup := keepWalk_nodup hkeep _
      chain := keepWalk_chain hkeep _
      closes := keepWalk_closes hkeep _ _
      mem_iff := mem_keepWalk_iff hkeep hM hN hx₀
      turn := keepWalk_turn_mem hkeep _ }, ?_⟩
  intro i hi m hm hk hfirst
  exact keepWalk_turn_next hkeep _ i hi m hm hk hfirst

end Walk

end PocketOrbit

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.keepWalk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.length_keepWalk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.getElem_keepWalk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.keepWalk_getElem_succ_mod
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.keepWalk_ne_nil
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.keepWalk_nodup
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.keepWalk_step
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.keepWalk_chain
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.keepWalk_closes
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.mem_keepWalk_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.keepWalk_turn_next
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.keepWalk_turn_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.exists_pocketOrbit_of_connected
