import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCAllPerm
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCompleteAll
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVFPLetters
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenConj
import GroupApproximation.Meta.AxiomGuard

/-!
# Faithfulness of the all-swaps presentation on one antichain (lane bh-met-77c)

Let `C` be a finite antichain of words over `Fin d` (no member is a prefix of another member),
with `0 < d`.  Words in the letters `(u, v)`, `u, v ∈ C`, are included into the all-swaps free
group by `higmanVCAll_iota`.  The cone swaps `(u v)` then permute the cones of `C`, so each such
word `r` moves the cone at `c ∈ C` onto the cone at `π r c`, where `π` is the transposition
evaluation into `Equiv.Perm C` (`higmanVCAll_mapsCone_word`).  Hence, if `r` evaluates to `1` in
`V_d`, then `π r = 1` (`higmanVCAll_pi_eq_one`).

In the quotient by the standard relators, the images `t u v` of the letters satisfy
`t u u = 1`, `(t u v)² = 1` and `t u v * t c e * (t u v)⁻¹ = t (π(u v) c) (π(u v) e)`: these are
the relator families (comparable letters), (involutions) and (conjugations).  By the
transposition presentation of `Equiv.Perm C` (`higmanVCAll_lift_eq_one`) such a word is a
consequence of the standard relators (`higmanVCAll_antichain_mem`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Distinct members of an antichain are not prefixes of one another. -/
theorem higmanVCAll_incomp {d : ℕ} {C : Finset (List (Fin d))}
    (hC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → ¬ u <+: v) {a b : ↥C} (hab : a ≠ b) : ¬ a.1 <+: b.1 :=
  hC a.1 a.2 b.1 b.2 fun h => hab (Subtype.ext h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_incomp

/-- Two members of an antichain whose cones share a stream are equal. -/
theorem higmanVCAll_eq_of_prepend {d : ℕ} {C : Finset (List (Fin d))}
    (hC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → ¬ u <+: v) {a b : ↥C} (s : Cantor (Fin d))
    (hs : prepend a.1 s = prepend b.1 s) : a = b := by
  by_contra hne
  have h2 : IsStreamPrefix b.1 (prepend a.1 s) := by
    rw [hs]
    exact isStreamPrefix_prepend b.1 s
  rcases prefix_or_prefix_of_isStreamPrefix (isStreamPrefix_prepend a.1 s) h2 with h3 | h3
  · exact hC a.1 a.2 b.1 b.2 (fun h => hne (Subtype.ext h)) h3
  · exact hC b.1 b.2 a.1 a.2 (fun h => hne (Subtype.ext h).symm) h3

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_eq_of_prepend

/-- The inclusion of the free group on pairs of members of `C` into the all-swaps free
group. -/
noncomputable def higmanVCAll_iota {d : ℕ} (C : Finset (List (Fin d))) :
    FreeGroup (↥C × ↥C) →* FreeGroup (List (Fin d) × List (Fin d)) :=
  FreeGroup.lift fun p : ↥C × ↥C => FreeGroup.of (p.1.1, p.2.1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_iota

/-- The inclusion on generators. -/
theorem higmanVCAll_iota_of {d : ℕ} (C : Finset (List (Fin d))) (p : ↥C × ↥C) :
    higmanVCAll_iota C (FreeGroup.of p) = FreeGroup.of (p.1.1, p.2.1) :=
  FreeGroup.lift_apply_of (f := fun p : ↥C × ↥C => FreeGroup.of (p.1.1, p.2.1))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_iota_of

/-- The letter `(a, b)` moves the cone at `c ∈ C` onto the cone at `swap a b c`. -/
theorem higmanVCAll_mapsCone_gen {d : ℕ} {C : Finset (List (Fin d))}
    (hC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → ¬ u <+: v) (a b c : ↥C) :
    MapsCone ((vgenSwapOrOne a.1 b.1 : ↥(higmanThompsonV (Fin d))) :
      Equiv.Perm (Cantor (Fin d))) c.1 (Equiv.swap a b c).1 := by
  by_cases hab : a = b
  · rw [hab, Equiv.swap_self, Equiv.refl_apply,
      higmanVFP_swapOrOne_of_not (fun h => h.1 (List.prefix_refl b.1))]
    exact mapsCone_one c.1
  have h1 := higmanVCAll_incomp hC hab
  have h2 := higmanVCAll_incomp hC (Ne.symm hab)
  rw [vgenSwapOrOne_eq h1 h2]
  by_cases hca : c = a
  · rw [hca, Equiv.swap_apply_left]
    exact mapsCone_coneSwap_left h1 h2
  by_cases hcb : c = b
  · rw [hcb, Equiv.swap_apply_right]
    exact mapsCone_coneSwap_right h1 h2
  rw [Equiv.swap_apply_of_ne_of_ne hca hcb]
  exact vgen_mapsCone_coneSwap_fix h1 h2 (higmanVCAll_incomp hC hca)
    (higmanVCAll_incomp hC (Ne.symm hca)) (higmanVCAll_incomp hC hcb)
    (higmanVCAll_incomp hC (Ne.symm hcb))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_mapsCone_gen

/-- **Cone tracking.**  The evaluation of `ι r` moves the cone at `c ∈ C` onto the cone at
`π r c`. -/
theorem higmanVCAll_mapsCone_word {d : ℕ} {C : Finset (List (Fin d))}
    (hC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → ¬ u <+: v) (r : FreeGroup (↥C × ↥C)) :
    ∀ c : ↥C, MapsCone ((higmanVC_evalAll d (higmanVCAll_iota C r) :
      ↥(higmanThompsonV (Fin d))) : Equiv.Perm (Cantor (Fin d))) c.1
      (FreeGroup.lift (fun p : ↥C × ↥C => Equiv.swap p.1 p.2) r c).1 := by
  induction r using FreeGroup.induction_on with
  | C1 =>
    intro c
    simp only [map_one, Subgroup.coe_one, Equiv.Perm.one_apply]
    exact mapsCone_one c.1
  | of x =>
    intro c
    rw [higmanVCAll_iota_of, higmanVC_evalAll_of, FreeGroup.lift_apply_of]
    exact higmanVCAll_mapsCone_gen hC x.1 x.2 c
  | inv_of x _ =>
    intro c
    rw [map_inv, map_inv, map_inv, higmanVCAll_iota_of, higmanVC_evalAll_of,
      FreeGroup.lift_apply_of, Equiv.swap_inv]
    have h := higmanVCAll_mapsCone_gen hC x.1 x.2 (Equiv.swap x.1 x.2 c)
    rw [Equiv.swap_apply_self] at h
    exact h.inv
  | mul x y hx hy =>
    intro c
    rw [map_mul, map_mul, map_mul, Subgroup.coe_mul, Equiv.Perm.mul_apply]
    exact MapsCone.comp (hy c) (hx _)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_mapsCone_word

/-- **Faithfulness of `π`.**  A word in the letters of `C` that is trivial in `V_d` induces the
trivial permutation of `C`. -/
theorem higmanVCAll_pi_eq_one {d : ℕ} (hd : 0 < d) {C : Finset (List (Fin d))}
    (hC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → ¬ u <+: v) (r : FreeGroup (↥C × ↥C))
    (hr : higmanVC_evalAll d (higmanVCAll_iota C r) = 1) :
    FreeGroup.lift (fun p : ↥C × ↥C => Equiv.swap p.1 p.2) r = 1 := by
  refine Equiv.ext fun c => ?_
  rw [Equiv.Perm.one_apply]
  obtain ⟨s⟩ : Nonempty (Cantor (Fin d)) := ⟨fun _ => ⟨0, hd⟩⟩
  have h : ((higmanVC_evalAll d (higmanVCAll_iota C r) : ↥(higmanThompsonV (Fin d))) :
      Equiv.Perm (Cantor (Fin d))) (prepend c.1 s) =
      prepend (FreeGroup.lift (fun p : ↥C × ↥C => Equiv.swap p.1 p.2) r c).1 s :=
    higmanVCAll_mapsCone_word hC r c s
  rw [hr] at h
  simp only [Subgroup.coe_one, Equiv.Perm.one_apply] at h
  exact (higmanVCAll_eq_of_prepend (a := c)
    (b := FreeGroup.lift (fun p : ↥C × ↥C => Equiv.swap p.1 p.2) r c) hC s h).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_pi_eq_one

/-- The image of the letter `(a, b)`, `a, b ∈ C`, in the quotient by the standard relators. -/
noncomputable def higmanVCAll_gen (d : ℕ) (C : Finset (List (Fin d))) (a b : ↥C) :
    FreeGroup (List (Fin d) × List (Fin d)) ⧸
      Subgroup.normalClosure (higmanVC_rels d fun _ => True) :=
  QuotientGroup.mk' (Subgroup.normalClosure (higmanVC_rels d fun _ => True))
    (FreeGroup.of (a.1, b.1))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_gen

/-- Relator family (comparable letters): `t a a = 1`. -/
theorem higmanVCAll_gen_self {d : ℕ} {C : Finset (List (Fin d))} (a : ↥C) :
    higmanVCAll_gen d C a a = 1 := by
  rw [higmanVCAll_gen, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  refine Subgroup.subset_normalClosure ?_
  rw [higmanVC_rels, Set.mem_setOf_eq]
  exact Or.inl ⟨a.1, a.1, trivial, trivial, fun h => h.1 (List.prefix_refl a.1), rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_gen_self

/-- Relator family (involutions): `t a b * t a b = 1`. -/
theorem higmanVCAll_gen_sq {d : ℕ} {C : Finset (List (Fin d))} (a b : ↥C) :
    higmanVCAll_gen d C a b * higmanVCAll_gen d C a b = 1 := by
  rw [higmanVCAll_gen, ← map_mul, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  refine Subgroup.subset_normalClosure ?_
  rw [higmanVC_rels, Set.mem_setOf_eq]
  exact Or.inr (Or.inl ⟨a.1, b.1, trivial, trivial, rfl⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_gen_sq

/-- The letter `(a, b)` with `a ≠ b` carries the cone at `c` onto the cone at `swap a b c`. -/
theorem higmanVCAll_mapsCone_coneSwap {d : ℕ} {C : Finset (List (Fin d))}
    (hC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → ¬ u <+: v) {a b : ↥C} (hpq : ¬ a.1 <+: b.1)
    (hqp : ¬ b.1 <+: a.1) (c : ↥C) :
    MapsCone (coneSwap a.1 b.1 hpq hqp) c.1 (Equiv.swap a b c).1 := by
  have h := higmanVCAll_mapsCone_gen hC a b c
  rw [vgenSwapOrOne_eq hpq hqp] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_mapsCone_coneSwap

/-- Relator family (conjugations):
`t a b * t c e * (t a b)⁻¹ = t (swap a b c) (swap a b e)`. -/
theorem higmanVCAll_gen_conj {d : ℕ} {C : Finset (List (Fin d))}
    (hC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → ¬ u <+: v) (a b c e : ↥C) :
    higmanVCAll_gen d C a b * higmanVCAll_gen d C c e * (higmanVCAll_gen d C a b)⁻¹ =
      higmanVCAll_gen d C (Equiv.swap a b c) (Equiv.swap a b e) := by
  by_cases hab : a = b
  · rw [hab, higmanVCAll_gen_self]
    simp only [Equiv.swap_self, Equiv.refl_apply, one_mul, inv_one, mul_one]
  by_cases hce : c = e
  · rw [hce, higmanVCAll_gen_self, higmanVCAll_gen_self, mul_one, mul_inv_cancel]
  have hpq := higmanVCAll_incomp hC hab
  have hqp := higmanVCAll_incomp hC (Ne.symm hab)
  have hce' : Equiv.swap a b c ≠ Equiv.swap a b e := (Equiv.swap a b).injective.ne hce
  have hmem : FreeGroup.of (a.1, b.1) * FreeGroup.of (c.1, e.1) * (FreeGroup.of (a.1, b.1))⁻¹ *
      (FreeGroup.of ((Equiv.swap a b c).1, (Equiv.swap a b e).1))⁻¹ ∈
      higmanVC_rels d fun _ => True := by
    rw [higmanVC_rels, Set.mem_setOf_eq]
    exact Or.inr (Or.inr (Or.inl ⟨a.1, b.1, c.1, e.1, (Equiv.swap a b c).1,
      (Equiv.swap a b e).1, trivial, trivial, trivial, trivial, trivial, trivial, hpq, hqp,
      higmanVCAll_mapsCone_coneSwap hC hpq hqp c, higmanVCAll_mapsCone_coneSwap hC hpq hqp e,
      higmanVCAll_incomp hC hce, higmanVCAll_incomp hC (Ne.symm hce),
      higmanVCAll_incomp hC hce', higmanVCAll_incomp hC (Ne.symm hce'), rfl⟩))
  have hk := Subgroup.subset_normalClosure hmem
  rw [SetLike.mem_coe, ← QuotientGroup.ker_mk'
      (Subgroup.normalClosure (higmanVC_rels d fun _ => True)), MonoidHom.mem_ker,
    map_mul, map_mul, map_mul, map_inv, map_inv] at hk
  exact mul_inv_eq_one.mp hk

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_gen_conj

/-- The quotient map after the inclusion of `C` is the evaluation `(a, b) ↦ t a b`. -/
theorem higmanVCAll_mk_iota {d : ℕ} (C : Finset (List (Fin d))) (r : FreeGroup (↥C × ↥C)) :
    QuotientGroup.mk' (Subgroup.normalClosure (higmanVC_rels d fun _ => True))
        (higmanVCAll_iota C r) =
      FreeGroup.lift (fun p : ↥C × ↥C => higmanVCAll_gen d C p.1 p.2) r :=
  DFunLike.congr_fun (FreeGroup.ext_hom
    ((QuotientGroup.mk' (Subgroup.normalClosure (higmanVC_rels d fun _ => True))).comp
      (higmanVCAll_iota C))
    (FreeGroup.lift fun p : ↥C × ↥C => higmanVCAll_gen d C p.1 p.2)
    fun p => by
      rw [MonoidHom.comp_apply, higmanVCAll_iota_of, FreeGroup.lift_apply_of, higmanVCAll_gen])
    r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_mk_iota

/-- **Faithfulness on an antichain.**  If `C` is a finite antichain and a word `r` in the
letters of `C` evaluates to `1` in `V_d`, then `ι r` is a consequence of the standard
relators. -/
theorem higmanVCAll_antichain_mem {d : ℕ} (hd : 0 < d) (C : Finset (List (Fin d)))
    (hC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → ¬ u <+: v) (r : FreeGroup (↥C × ↥C))
    (hr : higmanVC_evalAll d (higmanVCAll_iota C r) = 1) :
    higmanVCAll_iota C r ∈ Subgroup.normalClosure (higmanVC_rels d fun _ => True) := by
  rw [← QuotientGroup.ker_mk' (Subgroup.normalClosure (higmanVC_rels d fun _ => True)),
    MonoidHom.mem_ker, higmanVCAll_mk_iota]
  exact higmanVCAll_lift_eq_one (higmanVCAll_gen d C) higmanVCAll_gen_self higmanVCAll_gen_sq
    (higmanVCAll_gen_conj hC) r (higmanVCAll_pi_eq_one hd hC r hr)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_antichain_mem

end GroupApproximation.BooneHigman.Metabelian.Envelope
