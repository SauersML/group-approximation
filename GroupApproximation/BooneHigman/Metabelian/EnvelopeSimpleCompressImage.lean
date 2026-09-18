import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleGap
import GroupApproximation.Meta.AxiomGuard

/-!
# Elements of `V_X(H)` carry sets missing a cone to sets missing a cone

First half of clause (C) (`RNCompressStatement`): `MissesCone` is invariant under
`roverNekrashevych X H`.

Route: `ConeInImage f` says that the image under `f` of every cone contains a cone.  It holds
for elements of some depth (`coneInImage_of_hasDepth`), for tree automorphisms
(`coneInImage_cantorHom`), is preserved by `localize` and by products, so by closure induction
on `ConeInImage g ∧ ConeInImage g⁻¹` it holds on `V_X(H)` (`coneInImage_rn_and_inv`).
If `S` misses `cone c` and `cone c' ⊆ f '' cone c`, then `f '' S` misses `cone c'`
(`missesCone_image_rn`).  Self-similarity is not used.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open scoped commutatorElement
open Trees

variable {X : Type*}

/-- The image of every cone contains a cone. -/
def ConeInImage (f : Equiv.Perm (Cantor X)) : Prop :=
  ∀ c : List X, ∃ c' : List X, cone c' ⊆ f '' cone c

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.ConeInImage

theorem coneInImage_one : ConeInImage (1 : Equiv.Perm (Cantor X)) :=
  fun c => ⟨c, fun p hp => ⟨p, hp, rfl⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneInImage_one

theorem ConeInImage.mul {f g : Equiv.Perm (Cantor X)} (hf : ConeInImage f)
    (hg : ConeInImage g) : ConeInImage (f * g) := by
  intro c
  obtain ⟨c₁, h₁⟩ := hg c
  obtain ⟨c₂, h₂⟩ := hf c₁
  refine ⟨c₂, fun p hp => ?_⟩
  obtain ⟨q, hq, rfl⟩ := h₂ hp
  obtain ⟨r, hr, rfl⟩ := h₁ hq
  exact ⟨r, hr, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.ConeInImage.mul

theorem coneInImage_of_hasDepth (a : X) {f : Equiv.Perm (Cantor X)} {N : ℕ}
    (hf : HasDepth f N) : ConeInImage f := by
  intro c
  obtain ⟨v, hv⟩ := hf.mono (Nat.le_add_left N c.length) (c ++ List.replicate N a)
    (by simp only [List.length_append, List.length_replicate])
  refine ⟨v, ?_⟩
  rw [← hv.image_cone]
  exact Set.image_mono (cone_append_subset c _)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneInImage_of_hasDepth

theorem firstWord_length_of_isStreamPrefix {w : List X} {p : Cantor X}
    (hp : IsStreamPrefix w p) : firstWord w.length p = w := by
  have h := firstWord_length_prepend w (dropN w.length p)
  rwa [prepend_dropN_of_isStreamPrefix w p hp] at h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.firstWord_length_of_isStreamPrefix

theorem coneInImage_cantorHom (g : TreeAut X) : ConeInImage (cantorHom g) := by
  intro c
  refine ⟨g • c, fun p hp => ⟨cantorHom g⁻¹ p, ?_, ?_⟩⟩
  · have hw : firstWord c.length (cantorHom g⁻¹ p) = c := by
      rw [cantorHom_apply, firstWord_streamFun, ← TreeAut.length_smul g c,
        firstWord_length_of_isStreamPrefix (w := g • c) (p := p) hp, inv_smul_smul]
    have h := isStreamPrefix_firstWord c.length (cantorHom g⁻¹ p)
    rw [hw] at h
    exact h
  · rw [cantorHom_apply, cantorHom_apply, ← streamFun_mul, mul_inv_cancel, streamFun_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneInImage_cantorHom

theorem coneInImage_localize {g : Equiv.Perm (Cantor X)} (hg : ConeInImage g) (w : List X) :
    ConeInImage (localize w g) := by
  intro c
  by_cases hwc : w <+: c
  · obtain ⟨r, rfl⟩ := hwc
    obtain ⟨r', hr'⟩ := hg r
    refine ⟨w ++ r', fun p hp => ?_⟩
    obtain ⟨z, rfl⟩ := mem_cone_iff.mp hp
    obtain ⟨q, hq, hqz⟩ := hr' (prepend_mem_cone r' z)
    obtain ⟨y, rfl⟩ := mem_cone_iff.mp hq
    refine ⟨prepend (w ++ r) y, prepend_mem_cone (w ++ r) y, ?_⟩
    rw [prepend_append w r y, localize_apply_prepend, hqz, prepend_append w r' z]
  · by_cases hcw : c <+: w
    · refine ⟨w, fun p hp => ?_⟩
      obtain ⟨z, rfl⟩ := mem_cone_iff.mp hp
      refine ⟨prepend w (g.symm z), cone_subset_of_prefix hcw (prepend_mem_cone w _), ?_⟩
      rw [localize_apply_prepend, Equiv.apply_symm_apply g z]
    · refine ⟨c, fun p hp => ⟨p, hp, ?_⟩⟩
      exact localize_apply_of_not
        (fun h => Set.disjoint_right.mp (disjoint_cone hwc hcw) hp h) g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneInImage_localize

theorem coneInImage_rn_and_inv [Finite X] (a : X) (H : Subgroup (TreeAut X))
    {f : Equiv.Perm (Cantor X)} (hf : f ∈ roverNekrashevych X H) :
    ConeInImage f ∧ ConeInImage f⁻¹ := by
  have hf' : f ∈ Subgroup.closure (rnGenerators H) := hf
  clear hf
  induction hf' using Subgroup.closure_induction with
  | mem x hx =>
      have hx' : x ∈ (higmanThompsonV X : Set (Equiv.Perm (Cantor X))) ∪
          {g | ∃ w : List X, ∃ h ∈ H, g = localize w (cantorHom h)} := hx
      rcases hx' with hV | ⟨w, h, _, rfl⟩
      · obtain ⟨N, hN⟩ := mem_higmanThompsonV.mp (SetLike.mem_coe.mp hV)
        obtain ⟨M, hM⟩ := hN.exists_inv
        exact ⟨coneInImage_of_hasDepth a hN, coneInImage_of_hasDepth a hM⟩
      · refine ⟨coneInImage_localize (coneInImage_cantorHom h) w, ?_⟩
        rw [← map_inv (localize w) (cantorHom h), ← map_inv cantorHom h]
        exact coneInImage_localize (coneInImage_cantorHom h⁻¹) w
  | one =>
      refine ⟨coneInImage_one, ?_⟩
      rw [inv_one]
      exact coneInImage_one
  | mul x y _ _ hx hy =>
      refine ⟨hx.1.mul hy.1, ?_⟩
      rw [mul_inv_rev]
      exact hy.2.mul hx.2
  | inv x _ hx =>
      rw [inv_inv]
      exact ⟨hx.2, hx.1⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneInImage_rn_and_inv

/-- **Invariance of `MissesCone`** under `V_X(H)`. -/
theorem missesCone_image_rn [Finite X] [Nontrivial X] (H : Subgroup (TreeAut X))
    {S : Set (Cantor X)} (hS : MissesCone S) {f : Equiv.Perm (Cantor X)}
    (hf : f ∈ roverNekrashevych X H) : MissesCone (f '' S) := by
  obtain ⟨a, -, -⟩ := exists_pair_ne X
  obtain ⟨c, hc⟩ := hS
  obtain ⟨c', hc'⟩ := (coneInImage_rn_and_inv a H hf).1 c
  refine ⟨c', Set.disjoint_left.mpr ?_⟩
  rintro p ⟨s, hs, rfl⟩ hp
  obtain ⟨q, hq, hqs⟩ := hc' hp
  obtain rfl := Equiv.injective f hqs
  exact Set.disjoint_left.mp hc hs hq

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.missesCone_image_rn

end GroupApproximation.BooneHigman.Metabelian.Envelope
