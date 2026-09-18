import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsKernelFinal
import GroupApproximation.Meta.AxiomGuard

/-!
# Normal form: incomparable words and commuting factors

Word combinatorics and quotient algebra used to rewrite words of `RNFree X H` into normal
form.
* `rnNF_incomp_mono`: incomparability passes to extensions of the two words.
* `rnNF_incomp_of_length`: distinct words of one length are incomparable.
* `rnNF_incomp_image`: a map carrying two cones onto cones keeps them incomparable.
* `rnNF_not_isStreamPrefix`: a stream through `cone c`, where `w <+: c`, avoids every cone
  incomparable with `w`.
* `rnNF_commute_rfV`: `rfV s` commutes with `rfConjL e k` when `s` fixes the cone of `e`.
* `rnNF_rfConjL_mul_same`: factors on the same cone multiply to one factor.
* `rnNF_conj_prod`: conjugation distributes over a list product.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

variable {X : Type*}

/-- Incomparability passes to extensions. -/
theorem rnNF_incomp_mono {a a' b b' : List X} (ha : a <+: a') (hb : b <+: b')
    (h : ¬ a <+: b ∧ ¬ b <+: a) : ¬ a' <+: b' ∧ ¬ b' <+: a' := by
  constructor
  · intro h'
    exact (List.prefix_or_prefix_of_prefix (ha.trans h') hb).elim h.1 h.2
  · intro h'
    exact (List.prefix_or_prefix_of_prefix ha (hb.trans h')).elim h.1 h.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_incomp_mono

/-- Distinct words of one length are incomparable. -/
theorem rnNF_incomp_of_length {a b : List X} (hlen : a.length = b.length) (hne : a ≠ b) :
    ¬ a <+: b ∧ ¬ b <+: a :=
  ⟨fun h => hne (h.eq_of_length hlen), fun h => hne (h.eq_of_length hlen.symm).symm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_incomp_of_length

/-- If the images of two cones are comparable, so are the cones. -/
theorem rnNF_comp_of_image [Nonempty X] {g : Equiv.Perm (Cantor X)} {a a' b b' : List X}
    (ha : MapsCone g a a') (hb : MapsCone g b b') (hpre : a' <+: b') : a <+: b ∨ b <+: a := by
  obtain ⟨t, rfl⟩ := hpre
  have y : Cantor X := fun _ => Classical.arbitrary X
  have heq : prepend b y = prepend a (prepend t y) :=
    g.injective (by rw [hb y, ha (prepend t y), prepend_append])
  have hs := isStreamPrefix_prepend a (prepend t y)
  rw [← heq] at hs
  exact prefix_or_prefix_of_isStreamPrefix hs (isStreamPrefix_prepend b y)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_comp_of_image

/-- A map carrying two incomparable cones onto cones keeps them incomparable. -/
theorem rnNF_incomp_image [Nonempty X] {g : Equiv.Perm (Cantor X)} {a a' b b' : List X}
    (ha : MapsCone g a a') (hb : MapsCone g b b') (h : ¬ a <+: b ∧ ¬ b <+: a) :
    ¬ a' <+: b' ∧ ¬ b' <+: a' :=
  ⟨fun h' => (rnNF_comp_of_image ha hb h').elim h.1 h.2,
    fun h' => (rnNF_comp_of_image hb ha h').elim h.2 h.1⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_incomp_image

/-- A stream through `cone c`, with `w <+: c`, avoids every cone incomparable with `w`. -/
theorem rnNF_not_isStreamPrefix {u w c : List X} (hwc : w <+: c) (hi : ¬ u <+: w ∧ ¬ w <+: u)
    (y : Cantor X) : ¬ IsStreamPrefix u (prepend c y) := fun hu =>
  (prefix_or_prefix_of_isStreamPrefix hu
    (IsStreamPrefix.of_prefix hwc (isStreamPrefix_prepend c y))).elim hi.1 hi.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_not_isStreamPrefix

/-- Conjugation distributes over a list product. -/
theorem rnNF_conj_prod {G ι : Type*} [Group G] (g : G) (f : ι → G) (L : List ι) :
    g * (L.map f).prod * g⁻¹ = (L.map fun a => g * f a * g⁻¹).prod := by
  induction L with
  | nil => simp only [List.map_nil, List.prod_nil, mul_one, mul_inv_cancel]
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← ih]
    simp only [mul_assoc, inv_mul_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_conj_prod

variable [Finite X]

/-- `rfV s` commutes with a factor whose cone `s` fixes. -/
theorem rnNF_commute_rfV (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N) {s e : ↥(higmanThompsonV X)} {c : List X}
    (hs : MapsCone (s : Equiv.Perm (Cantor X)) c c)
    (he : MapsCone (e : Equiv.Perm (Cantor X)) [x₀] c) (k : ↥H) :
    Commute (rfV H N s) (rfConjL H N e k) := by
  have h1 := rcore_conj_rfConjL H N s e k
  rw [rcore_rfConjL_congr H N x₀ hcomm (e₁ := e) (e₂ := s * e) he (he.comp hs) k] at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_commute_rfV

/-- `rfV s` commutes with a product of factors whose cones `s` fixes. -/
theorem rnNF_commute_rfV_prod (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H))
    [N.Normal] (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N) (s : ↥(higmanThompsonV X))
    (P : List (↥(higmanThompsonV X) × List X × ↥H))
    (hP : ∀ p ∈ P, MapsCone (p.1 : Equiv.Perm (Cantor X)) [x₀] p.2.1)
    (hs : ∀ p ∈ P, MapsCone (s : Equiv.Perm (Cantor X)) p.2.1 p.2.1) :
    Commute (rfV H N s) (P.map fun p => rfConjL H N p.1 p.2.2).prod := by
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
  exact rnNF_commute_rfV H N x₀ hcomm (hs p hp) (hP p hp) p.2.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_commute_rfV_prod

/-- Two factors on the same cone multiply to one factor. -/
theorem rnNF_rfConjL_mul_same (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H))
    [N.Normal] (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N) {e e' : ↥(higmanThompsonV X)}
    {w : List X} (he : MapsCone (e : Equiv.Perm (Cantor X)) [x₀] w)
    (he' : MapsCone (e' : Equiv.Perm (Cantor X)) [x₀] w) (h h' : ↥H) :
    rfConjL H N e h * rfConjL H N e' h' = rfConjL H N e (h * h') := by
  rw [rcore_rfConjL_congr H N x₀ hcomm (e₁ := e) (e₂ := e') he he' h', map_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_rfConjL_mul_same

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
