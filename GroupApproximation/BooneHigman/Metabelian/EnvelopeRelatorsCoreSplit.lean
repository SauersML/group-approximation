import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsCoreProd
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite core relators: splitting relators on generators (step 4)

Fix `N ⊴ RNFree X H` containing all commutation and all disjoint-cone relators, a list `l` of
`X` without repetition and a word `u`.  In `Q = RNFree X H ⧸ N` put
`rcoreW h = rfV (rcoreShift u (rootPerm h)) * Π_{x ∈ l} rfConjL (rcoreE x₀ (u ++ [x])) (h|_x)`.
* `rcoreW_mul`: `rcoreW` is multiplicative, by the cocycle rule `rcoreSt_mul`, conjugation by
  the shift (`rcore_shift_conj`) and commutation of local copies on the incomparable cones
  `u ++ [x]` (`rcore_commute_rfConjL_incomp`).
* `rcore_image_eq`: every splitting-type relator `(β h)⁻¹ * nfV a * Π nfV (c x) * nfL (k x) *
  (nfV (c x))⁻¹` maps to `(β h)⁻¹ * rcoreW h` in `Q`.
* `rcore_relators_of_gen`: if the canonical relators hold for a generating set of `H`, every
  relator of this shape lies in `N` (`MonoidHom.eq_of_eqOn_dense`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

variable {X : Type*} [Finite X]

theorem rcore_E_append_spec [Nontrivial X] (x₀ : X) (u : List X) (x : X) :
    MapsCone (rcoreE x₀ (u ++ [x]) : Equiv.Perm (Cantor X)) [x₀] (u ++ [x]) :=
  rcoreE_spec x₀ (List.append_ne_nil_of_right_ne_nil u (List.cons_ne_nil x []))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_E_append_spec

theorem rcore_commute_append [Nontrivial X] (H : Subgroup (TreeAut X))
    (N : Subgroup (RNFree X H)) [N.Normal] (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N)
    (hdisj : nfDisjRelators H x₀ ⊆ N) (u : List X) {x y : X} (hxy : x ≠ y) (h k : ↥H) :
    Commute (rfConjL H N (rcoreE x₀ (u ++ [x])) h) (rfConjL H N (rcoreE x₀ (u ++ [y])) k) :=
  rcore_commute_rfConjL_incomp H N x₀ hcomm hdisj (rcore_append_singleton_incomp hxy u)
    (rcore_append_singleton_incomp hxy.symm u) (rcore_E_append_spec x₀ u x)
    (rcore_E_append_spec x₀ u y) h k

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_commute_append

/-- Conjugating by the shift `σ` permutes the local copies along `σ`. -/
theorem rcore_shift_conj [Nontrivial X] (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H))
    [N.Normal] (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N) (hdisj : nfDisjRelators H x₀ ⊆ N)
    {l : List X} (hl : l.Nodup) (hall : ∀ x, x ∈ l) (u : List X) (σ : Equiv.Perm X)
    (G : X → ↥H) :
    rfV H N (rcoreShift u σ) *
        (l.map fun x => rfConjL H N (rcoreE x₀ (u ++ [x])) (G (σ x))).prod *
        (rfV H N (rcoreShift u σ))⁻¹ =
      (l.map fun x => rfConjL H N (rcoreE x₀ (u ++ [x])) (G x)).prod := by
  have hterm : ∀ x, MulAut.conj (rfV H N (rcoreShift u σ))
      (rfConjL H N (rcoreE x₀ (u ++ [x])) (G (σ x))) =
      rfConjL H N (rcoreE x₀ (u ++ [σ x])) (G (σ x)) := fun x => by
    rw [MulAut.conj_apply, rcore_conj_rfConjL]
    exact rcore_rfConjL_congr H N x₀ hcomm (rcore_E_append_spec x₀ u (σ x))
      ((rcore_E_append_spec x₀ u x).comp (rcore_mapsCone_shift u σ x)) _
  rw [← MulAut.conj_apply, map_list_prod, List.map_map]
  have hmap : (l.map (⇑(MulAut.conj (rfV H N (rcoreShift u σ))) ∘
      fun x => rfConjL H N (rcoreE x₀ (u ++ [x])) (G (σ x)))) =
      ((l.map σ).map fun x => rfConjL H N (rcoreE x₀ (u ++ [x])) (G x)) := by
    rw [List.map_map]
    exact List.map_congr_left fun x _ => hterm x
  rw [hmap]
  exact rcore_prod_perm _ (List.Nodup.map σ.injective hl) hl
    (fun x => ⟨fun _ => hall x, fun _ => List.mem_map.mpr ⟨σ.symm x, hall _,
      σ.apply_symm_apply x⟩⟩)
    (fun x y hxy => rcore_commute_append H N x₀ hcomm hdisj u hxy (G x) (G y))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_shift_conj

/-- The candidate image of `h ∈ H`: a shift followed by the local copies of its states. -/
def rcoreW (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (hH : IsSelfSimilar H) (x₀ : X) (u l : List X) (h : ↥H) : RNFree X H ⧸ N :=
  rfV H N (rcoreShift u (TreeAut.rootPerm (h : TreeAut X))) *
    (l.map fun x => rfConjL H N (rcoreE x₀ (u ++ [x])) (rcoreSt H hH h x)).prod

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcoreW

theorem rcoreW_mul [Nontrivial X] (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H))
    [N.Normal] (hH : IsSelfSimilar H) (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N)
    (hdisj : nfDisjRelators H x₀ ⊆ N) {l : List X} (hl : l.Nodup) (hall : ∀ x, x ∈ l)
    (u : List X) (h k : ↥H) :
    rcoreW H N hH x₀ u l (h * k) = rcoreW H N hH x₀ u l h * rcoreW H N hH x₀ u l k := by
  have hconj := rcore_shift_conj H N x₀ hcomm hdisj hl hall u
    (TreeAut.rootPerm (k : TreeAut X)) (rcoreSt H hH h)
  have hmerge := rcore_prod_mul_prod
    (fun x => rfConjL H N (rcoreE x₀ (u ++ [x]))
      (rcoreSt H hH h (TreeAut.rootPerm (k : TreeAut X) x)))
    (fun x => rfConjL H N (rcoreE x₀ (u ++ [x])) (rcoreSt H hH k x)) l hl
    (fun x y hxy => rcore_commute_append H N x₀ hcomm hdisj u hxy _ _)
  simp only [rcoreW]
  rw [Subgroup.coe_mul, rcore_rootPerm_mul, rcoreShift_mul, map_mul (rfV H N), ← hconj]
  simp only [rcoreSt_mul, map_mul]
  rw [← hmerge]
  simp only [mul_assoc, inv_mul_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcoreW_mul

/-- `rcoreW` as a homomorphism `H →* RNFree X H ⧸ N`. -/
def rcoreWHom [Nontrivial X] (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H))
    [N.Normal] (hH : IsSelfSimilar H) (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N)
    (hdisj : nfDisjRelators H x₀ ⊆ N) {l : List X} (hl : l.Nodup) (hall : ∀ x, x ∈ l)
    (u : List X) : ↥H →* RNFree X H ⧸ N :=
  MonoidHom.mk' (rcoreW H N hH x₀ u l) (rcoreW_mul H N hH x₀ hcomm hdisj hl hall u)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcoreWHom

/-- The image in `RNFree X H ⧸ N` of a splitting-type word. -/
theorem rcore_mk_relator (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (y : RNFree X H) (a : ↥(higmanThompsonV X)) (c : X → ↥(higmanThompsonV X)) (k : X → ↥H)
    (l' : List X) :
    ((y⁻¹ * nfV H a * (l'.map fun x => nfV H (c x) * nfL H (k x) * (nfV H (c x))⁻¹).prod :
        RNFree X H) : RNFree X H ⧸ N) =
      (y : RNFree X H ⧸ N)⁻¹ * rfV H N a * (l'.map fun x => rfConjL H N (c x) (k x)).prod := by
  have hfun : (⇑(QuotientGroup.mk' N) ∘ fun x => nfV H (c x) * nfL H (k x) * (nfV H (c x))⁻¹) =
      fun x => rfConjL H N (c x) (k x) :=
    funext fun x => (rfConjL_apply H N (c x) (k x)).symm
  show QuotientGroup.mk' N _ = _
  rw [map_mul, map_mul, map_inv, map_list_prod, List.map_map, hfun]
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_mk_relator

/-- Every splitting-type word over `u` has image `rcoreW h` after its leading letter. -/
theorem rcore_image_eq [Nontrivial X] (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H))
    [N.Normal] (hH : IsSelfSimilar H) (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N)
    (hdisj : nfDisjRelators H x₀ ⊆ N) {l : List X} (hl : l.Nodup) (hall : ∀ x, x ∈ l)
    (u : List X) (h : ↥H) (a : ↥(higmanThompsonV X)) (c : X → ↥(higmanThompsonV X))
    (k : X → ↥H) {l' : List X} (hl' : l'.Nodup) (hall' : ∀ x, x ∈ l')
    (hk : ∀ x, (k x : TreeAut X) = TreeAut.state (h : TreeAut X) [x])
    (hc : ∀ x, MapsCone (c x : Equiv.Perm (Cantor X)) [x₀] (u ++ [x]))
    (ha : (a : Equiv.Perm (Cantor X)) = localize u (nfRootShift (TreeAut.rootPerm (h : TreeAut X)))) :
    rfV H N a * (l'.map fun x => rfConjL H N (c x) (k x)).prod = rcoreW H N hH x₀ u l h := by
  have ha' : a = rcoreShift u (TreeAut.rootPerm (h : TreeAut X)) := Subtype.ext ha
  have hk' : k = rcoreSt H hH h := funext fun x => Subtype.ext (hk x)
  subst ha' hk'
  have hprod : (l'.map fun x => rfConjL H N (c x) (rcoreSt H hH h x)) =
      l'.map fun x => rfConjL H N (rcoreE x₀ (u ++ [x])) (rcoreSt H hH h x) :=
    List.map_congr_left fun x _ =>
      rcore_rfConjL_congr H N x₀ hcomm (rcore_E_append_spec x₀ u x) (hc x) _
  rw [hprod, rcore_prod_perm (fun x => rfConjL H N (rcoreE x₀ (u ++ [x])) (rcoreSt H hH h x))
    hl' hl (fun x => ⟨fun _ => hall x, fun _ => hall' x⟩)
    (fun x y hxy => rcore_commute_append H N x₀ hcomm hdisj u hxy _ _)]
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_image_eq

/-- A splitting-type word whose leading letter maps to `rcoreW h` lies in `N`. -/
theorem rcore_relator_mem [Nontrivial X] (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H))
    [N.Normal] (hH : IsSelfSimilar H) (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N)
    (hdisj : nfDisjRelators H x₀ ⊆ N) {l : List X} (hl : l.Nodup) (hall : ∀ x, x ∈ l)
    (u : List X) (y : RNFree X H) (h : ↥H)
    (hy : (y : RNFree X H ⧸ N) = rcoreW H N hH x₀ u l h) (a : ↥(higmanThompsonV X))
    (c : X → ↥(higmanThompsonV X)) (k : X → ↥H) {l' : List X} (hl' : l'.Nodup)
    (hall' : ∀ x, x ∈ l') (hk : ∀ x, (k x : TreeAut X) = TreeAut.state (h : TreeAut X) [x])
    (hc : ∀ x, MapsCone (c x : Equiv.Perm (Cantor X)) [x₀] (u ++ [x]))
    (ha : (a : Equiv.Perm (Cantor X)) = localize u (nfRootShift (TreeAut.rootPerm (h : TreeAut X)))) :
    y⁻¹ * nfV H a * (l'.map fun x => nfV H (c x) * nfL H (k x) * (nfV H (c x))⁻¹).prod ∈ N := by
  refine (QuotientGroup.eq_one_iff (N := N) _).mp ?_
  rw [rcore_mk_relator H N y a c k l', mul_assoc,
    rcore_image_eq H N hH x₀ hcomm hdisj hl hall u h a c k hl' hall' hk hc ha, hy, inv_mul_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_relator_mem

/-- If the canonical splitting relators hold on a generating set `S` of `H`, the leading letter
`B` maps every `h` to `rcoreW h`. -/
theorem rcore_relators_of_gen [Nontrivial X] (H : Subgroup (TreeAut X))
    (N : Subgroup (RNFree X H)) [N.Normal] (hH : IsSelfSimilar H) (x₀ : X)
    (hcomm : nfCommRelators H x₀ ⊆ N) (hdisj : nfDisjRelators H x₀ ⊆ N) {l : List X}
    (hl : l.Nodup) (hall : ∀ x, x ∈ l) (u : List X) (B : ↥H →* RNFree X H) {S : Set ↥H}
    (hS : Subgroup.closure S = ⊤)
    (hgen : ∀ s ∈ S, (B s)⁻¹ * nfV H (rcoreShift u (TreeAut.rootPerm (s : TreeAut X))) *
      (l.map fun x => nfV H (rcoreE x₀ (u ++ [x])) * nfL H (rcoreSt H hH s x) *
        (nfV H (rcoreE x₀ (u ++ [x])))⁻¹).prod ∈ N) (h : ↥H) :
    ((B h : RNFree X H) : RNFree X H ⧸ N) = rcoreW H N hH x₀ u l h := by
  have hEq : (QuotientGroup.mk' N).comp B = rcoreWHom H N hH x₀ hcomm hdisj hl hall u := by
    refine MonoidHom.eq_of_eqOn_dense hS fun s hs => ?_
    have h1 := (QuotientGroup.eq_one_iff (N := N) _).mpr (hgen s hs)
    rw [rcore_mk_relator H N (B s) _ (fun x => rcoreE x₀ (u ++ [x])) (rcoreSt H hH s) l,
      mul_assoc] at h1
    exact inv_mul_eq_one.mp h1
  exact DFunLike.congr_fun hEq h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rcore_relators_of_gen

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
