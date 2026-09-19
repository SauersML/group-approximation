import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RealProjectiveSpace

/-!
# Topological properties of `RP n`

This file records the basic point-set topology of the antipodal quotient
`RP n`:

* the projection `proj n` is an open map (`proj_isOpenMap`) and hence an open
  quotient map (`proj_isOpenQuotientMap`);
* the projection `proj n` is also a closed map (`proj_isClosedMap`), being a
  continuous map from the compact sphere to the Hausdorff quotient;
* the defining relation of `RP n` is closed (`isClosed_proj_rel`);
* `RP n` is compact (`CompactSpace (RP n)`), as a quotient of the compact
  sphere;
* `RP n` is Hausdorff (`T2Space (RP n)`).

## Implementation notes

* **Openness** is proved via the saturation identity `proj_preimage_image`:
  the saturation of a set `U` under `proj n` is `U ∪ -U`, so it is open whenever
  `U` is. This is the standard argument that a quotient by a continuous
  involution is an open map.
* **Compactness** is in fact already provided by Mathlib's general instance
  `Quotient.compactSpace` (a quotient of a compact space is compact); the
  instance below merely re-exposes it for `RP n` and is discharged by
  `inferInstance`.
* **Hausdorffness** uses the general criterion
  `t2Space_iff_of_isOpenQuotientMap`: for an open quotient map the target is
  `T2` iff the relation `{(x, y) | proj x = proj y}` is closed. Here
  (`isClosed_proj_rel`) that relation is the union of the diagonal and the graph
  of the antipodal map, both of which are closed.

The saturation identity `proj_preimage_image` is an internal support lemma for
`proj_isOpenMap` and is marked `private`. The closed-relation fact
`isClosed_proj_rel` is exposed as public API (it is a standalone point-set fact:
the graph of the antipodal identification is closed), and it also feeds the
`T2Space` instance via `t2Space_iff_of_isOpenQuotientMap`. The remaining public
API is the open-map/closed-map/open-quotient-map facts together with the
`CompactSpace` and `T2Space` instances.
-/

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- The saturation of a set `U` under the projection `proj n` equals its union
with its antipode `-U`: `proj n ⁻¹' (proj n '' U) = U ∪ (fun x => -x) ⁻¹' U`.
Internal support lemma for `proj_isOpenMap`. -/
private theorem proj_preimage_image {n : ℕ} (U : Set (Sphere n)) :
    proj n ⁻¹' (proj n '' U) = U ∪ (fun x => -x) ⁻¹' U := by
  ext x
  constructor
  · rintro ⟨u, hu, hux⟩
    rcases Quotient.exact hux with h | h
    · left; rwa [h] at hu
    · right
      simp only [Set.mem_preimage]
      rw [← h]
      exact hu
  · rintro (hx | hx)
    · exact ⟨x, hx, rfl⟩
    · refine ⟨-x, hx, ?_⟩
      exact proj_neg x

/-- The projection `proj n` is an open map. -/
theorem proj_isOpenMap (n : ℕ) : IsOpenMap (proj n) := by
  intro U hU
  rw [← (proj_isQuotientMap n).isOpen_preimage, proj_preimage_image]
  exact hU.union (hU.preimage continuous_neg)

/-- The projection `proj n` is an open quotient map. -/
theorem proj_isOpenQuotientMap (n : ℕ) :
    IsOpenQuotientMap (proj n : Sphere n → RP n) :=
  ⟨proj_surjective n, (proj n).continuous, proj_isOpenMap n⟩

/-- `RP n` is compact, being a quotient of the compact sphere. (This also
follows from Mathlib's general instance `Quotient.compactSpace`.) -/
instance (n : ℕ) : CompactSpace (RP n) := by infer_instance

/-- The defining relation `{(x, y) | proj n x = proj n y}` of `RP n` is closed
in `Sphere n × Sphere n`: it is the union of the diagonal and the graph of the
antipodal map. This is the closed-relation input to
`t2Space_iff_of_isOpenQuotientMap` used by the `T2Space` instance below. -/
theorem isClosed_proj_rel (n : ℕ) :
    IsClosed {q : Sphere n × Sphere n | proj n q.1 = proj n q.2} := by
  have hset : {q : Sphere n × Sphere n | proj n q.1 = proj n q.2}
      = {q : Sphere n × Sphere n | q.1 = q.2} ∪ {q : Sphere n × Sphere n | q.1 = -q.2} := by
    ext q
    constructor
    · intro h
      rcases Quotient.exact h with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · rintro (h | h)
      · exact congrArg (proj n) h
      · show proj n q.1 = proj n q.2
        rw [h]; exact proj_neg q.2
  rw [hset]
  refine IsClosed.union isClosed_diagonal ?_
  have : {q : Sphere n × Sphere n | q.1 = -q.2}
      = {q : Sphere n × Sphere n | q.1 = (fun y => -y) q.2} := rfl
  rw [this]
  exact isClosed_eq continuous_fst (continuous_neg.comp continuous_snd)

/-- `RP n` is a Hausdorff space. -/
instance (n : ℕ) : T2Space (RP n) := by
  rw [t2Space_iff_of_isOpenQuotientMap (proj_isOpenQuotientMap n)]
  exact isClosed_proj_rel n

/-- The projection `proj n` is a closed map: a continuous map from the compact
sphere `Sphere n` to the Hausdorff quotient `RP n` is closed. -/
theorem proj_isClosedMap (n : ℕ) : IsClosedMap (proj n : Sphere n → RP n) :=
  (proj n).continuous.isClosedMap

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

