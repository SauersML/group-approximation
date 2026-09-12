import GroupApproximation.GGT.HullSCLemma51LetterPullbackClose

/-!
# The letter pullback by induction on the radius

`QuotientPeripheralLetterPullbackAt` asks for radii `R n` and factor counts `N n` such that every
element of the quotient relative ball of radius `n` is the image of a product of at most `N n`
atoms at radius `R n`.  It follows by induction on `n` from one move bound.

An element `y` of the quotient ball of radius `n + 1` lifts to a source word `p` of length at most
`n + 1`, whose image avoids `Γ_{q(H_λ)}`, and to `h ∈ H_λ` with `q (listVal p) = q h = y`
(`exists_lift_of_mem_relBall_mapSurjective`).

* If `listVal p = h`, then `h` lies in the source relative ball of radius `n + 1`, so it is an
  atom (`mem_relBall_of_avoids_mapHom`).
* Otherwise a move turns the quotient-null word `p ++ [comp λ h⁻¹]` into an outcome
  (`PullbackOutcome`) whose word read after the designated letter has length at most `n`, and
  `mem_image_of_pullbackOutcome` closes it with the induction hypothesis at radius `n`.

`LetterStepBound D W q hq P` is the move bound for the lifted words satisfying `P`, with radius
`R n` and count `N n`.  Two move bounds combine (`LetterStepBound.or`), so the move for words with
a non-geodesic rotation and the move for words all of whose rotations are geodesic are proved
separately.  `quotientPeripheralLetterPullbackAt_of_letterStepBound` is the induction, with the
radius `letterPullbackRadius R` and the count `letterPullbackCount N`.
-/

namespace GroupApproximation
namespace HullSC

universe u v w

variable {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}

/-- **A move bound for the lifted quotient-null words satisfying `P`.**  For a source word `p` of
length at most `n + 1` whose image avoids `Γ_{q(H_λ)}`, and `h ∈ H_λ` with `q (listVal p) = q h`
but `listVal p ≠ h`, the word `p ++ [comp λ h⁻¹]`, if it satisfies `P`, has an outcome at the
atoms of radius `R n` with count `N n`, whose word read after the designated letter has length at
most `n`. -/
def LetterStepBound (D : GGT.RelGenSet G Lambda) (W : Set (List (GGT.RelLetter G Lambda)))
    (q : G →* Q) (hq : Function.Surjective q) (P : List (GGT.RelLetter G Lambda) → Prop) :
    Prop :=
  ∃ R N : ℕ → ℕ, ∀ (lam : Lambda) (n : ℕ) (h : G) (p : List (GGT.RelLetter G Lambda)),
    h ∈ D.fam lam → (∀ a ∈ p, D.IsLetter a) → p.length ≤ n + 1 →
    GGT.AvoidsFrom (D.mapSurjective q hq).fam lam (p.map (GGT.RelLetter.mapHom q)) 1 →
    q (GGT.RelLetter.listVal p) = q h → GGT.RelLetter.listVal p ≠ h →
    P (p ++ [GGT.RelLetter.comp lam h⁻¹]) →
      PullbackOutcome D q hq lam (pullbackAtoms W D lam (R n)) (N n) h n

theorem DesignatedValue.mono {A A' : Set G} {N N' : ℕ} {h z : G}
    (hd : DesignatedValue A N h z) (hAA : A ⊆ A') (hNN : N ≤ N') :
    DesignatedValue A' N' h z := by
  obtain ⟨x, y, hx, hy, hz⟩ := hd
  exact ⟨x, y, boundedProducts_mono hAA hNN hx, boundedProducts_mono hAA hNN hy, hz⟩

/-- An outcome at fewer atoms or a smaller count is an outcome at more atoms or a larger count. -/
theorem PullbackOutcome.mono {D : GGT.RelGenSet G Lambda} {q : G →* Q}
    {hq : Function.Surjective q} {lam : Lambda} {A A' : Set G} {N N' : ℕ} {h : G} {m : ℕ}
    (hout : PullbackOutcome D q hq lam A N h m) (hAA : A ⊆ A') (hNN : N ≤ N') :
    PullbackOutcome D q hq lam A' N' h m := by
  rcases hout with ⟨t, ht, hqt⟩ |
    ⟨u₁, u₂, z, c, hlet, hnull, hlen, hcomp, hzcoset, hdes, hletters⟩
  · exact Or.inl ⟨t, boundedProducts_mono hAA hNN ht, hqt⟩
  · exact Or.inr ⟨u₁, u₂, z, c, hlet, hnull, hlen, hcomp, hzcoset, hdes.mono hAA hNN,
      hletters.mono (Set.image_mono (boundedProducts_mono hAA hNN))⟩

/-- **Two move bounds combine**, with the larger radius and the larger count. -/
theorem LetterStepBound.or {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {q : G →* Q} {hq : Function.Surjective q}
    {P P' : List (GGT.RelLetter G Lambda) → Prop} (hP : LetterStepBound D W q hq P)
    (hP' : LetterStepBound D W q hq P') : LetterStepBound D W q hq (fun w => P w ∨ P' w) := by
  obtain ⟨R, N, hRN⟩ := hP
  obtain ⟨R', N', hRN'⟩ := hP'
  refine ⟨fun n => max (R n) (R' n), fun n => max (N n) (N' n), ?_⟩
  intro lam n h p hh hp hlen havoid hqp hne hw
  rcases hw with hw | hw
  · exact (hRN lam n h p hh hp hlen havoid hqp hne hw).mono
      (pullbackAtoms_mono (le_max_left (R n) (R' n))) (le_max_left (N n) (N' n))
  · exact (hRN' lam n h p hh hp hlen havoid hqp hne hw).mono
      (pullbackAtoms_mono (le_max_right (R n) (R' n))) (le_max_right (N n) (N' n))

/-- **The radius of the induction.**  At `n + 1` it covers the radius at `n`, the radius of the
move at `n`, and the source ball of radius `n + 1`. -/
def letterPullbackRadius (R : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => max (letterPullbackRadius R n) (max (R n) (n + 1))

theorem letterPullbackRadius_succ (R : ℕ → ℕ) (n : ℕ) :
    letterPullbackRadius R (n + 1) = max (letterPullbackRadius R n) (max (R n) (n + 1)) := rfl

/-- **The factor count of the induction.**  At `n + 1` it covers the count `(n + 3) · max (N n) M`
of `mem_image_of_pullbackOutcome`, with `M` the count at `n`, and one factor. -/
def letterPullbackCount (N : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 3) * (N n + letterPullbackCount N n + 1)

theorem letterPullbackCount_succ (N : ℕ → ℕ) (n : ℕ) :
    letterPullbackCount N (n + 1) = (n + 3) * (N n + letterPullbackCount N n + 1) := rfl

/-- **The induction of the letter pullback**, radius by radius. -/
theorem relBall_mapSurjective_subset_of_letterStepBound {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {q : G →* Q} {hq : Function.Surjective q}
    {P : List (GGT.RelLetter G Lambda) → Prop} {R N : ℕ → ℕ}
    (hstep : ∀ (lam : Lambda) (n : ℕ) (h : G) (p : List (GGT.RelLetter G Lambda)),
      h ∈ D.fam lam → (∀ a ∈ p, D.IsLetter a) → p.length ≤ n + 1 →
      GGT.AvoidsFrom (D.mapSurjective q hq).fam lam (p.map (GGT.RelLetter.mapHom q)) 1 →
      q (GGT.RelLetter.listVal p) = q h → GGT.RelLetter.listVal p ≠ h →
      P (p ++ [GGT.RelLetter.comp lam h⁻¹]) →
        PullbackOutcome D q hq lam (pullbackAtoms W D lam (R n)) (N n) h n)
    (hP : ∀ w, P w) (lam : Lambda) (n : ℕ) :
    (D.mapSurjective q hq).relBall lam n ⊆
      q '' boundedProducts (pullbackAtoms W D lam (letterPullbackRadius R n))
        (letterPullbackCount N n) := by
  induction n with
  | zero =>
      intro y hy
      obtain ⟨p, _, hlen, hval, _, _⟩ := exists_lift_of_mem_relBall_mapSurjective D q hq hy
      rcases p with _ | ⟨a, t⟩
      · subst hval
        exact ⟨1, one_mem_boundedProducts _ _, rfl⟩
      · simp at hlen
  | succ n ih =>
      intro y hy
      obtain ⟨p, hp, hlen, hval, havoid, h, hh, hqh⟩ :=
        exists_lift_of_mem_relBall_mapSurjective D q hq hy
      have hqp : q (GGT.RelLetter.listVal p) = q h := by rw [hval, hqh]
      have hrad : letterPullbackRadius R (n + 1) =
          max (letterPullbackRadius R n) (max (R n) (n + 1)) := letterPullbackRadius_succ R n
      have hcnt : letterPullbackCount N (n + 1) =
          (n + 3) * (N n + letterPullbackCount N n + 1) := letterPullbackCount_succ N n
      rw [← hqh]
      by_cases hne : GGT.RelLetter.listVal p = h
      · have hsucc : n + 1 ≤ letterPullbackRadius R (n + 1) := by
          rw [hrad]
          exact le_max_of_le_right (le_max_right _ _)
        have hmem : h ∈ pullbackAtoms W D lam (letterPullbackRadius R (n + 1)) :=
          pullbackAtoms_mono hsucc (relBall_subset_pullbackAtoms W D lam (n + 1)
            (GGT.OsinComponents.relBall_mono_radius D lam hlen
              (mem_relBall_of_avoids_mapHom D q hq hp havoid hh hne)))
        have hone : 1 ≤ letterPullbackCount N (n + 1) := by
          rw [hcnt]
          exact le_trans (by omega : 1 ≤ N n + letterPullbackCount N n + 1)
            (le_mul_of_one_le_left (Nat.zero_le _) (by omega))
        exact ⟨h, mem_boundedProducts_of_mem hmem hone, rfl⟩
      · have hRn : letterPullbackRadius R n ≤ letterPullbackRadius R (n + 1) := by
          rw [hrad]
          exact le_max_left _ _
        have hRstep : R n ≤ letterPullbackRadius R (n + 1) := by
          rw [hrad]
          exact le_max_of_le_right (le_max_left _ _)
        have hball : (D.mapSurjective q hq).relBall lam n ⊆
            q '' boundedProducts (pullbackAtoms W D lam (letterPullbackRadius R (n + 1)))
              (letterPullbackCount N n) := fun z hz =>
          Set.image_mono (boundedProducts_mono (pullbackAtoms_mono hRn) le_rfl) (ih hz)
        have hclose := mem_image_of_pullbackOutcome D q hq (pullbackAtoms_mono hRstep)
          (fun _ hx => inv_mem_pullbackAtoms hx) hball
          (hstep lam n h p hh hp hlen havoid hqp hne (hP _))
        have hle : (n + 3) * max (N n) (letterPullbackCount N n) ≤
            letterPullbackCount N (n + 1) := by
          rw [hcnt]
          exact Nat.mul_le_mul (le_refl _) (max_le (by omega) (by omega))
        exact Set.image_mono (boundedProducts_mono (fun _ hb => hb) hle) hclose

/-- **The letter pullback from a move bound for every lifted word.** -/
theorem quotientPeripheralLetterPullbackAt_of_letterStepBound {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {q : G →* Q} {hq : Function.Surjective q}
    {P : List (GGT.RelLetter G Lambda) → Prop} (hstep : LetterStepBound D W q hq P)
    (hP : ∀ w, P w) : QuotientPeripheralLetterPullbackAt D W q hq := by
  obtain ⟨R, N, hRN⟩ := hstep
  exact ⟨letterPullbackRadius R, letterPullbackCount N, fun lam n =>
    relBall_mapSurjective_subset_of_letterStepBound hRN hP lam n⟩

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.DesignatedValue.mono
#audit_axioms GroupApproximation.HullSC.PullbackOutcome.mono
#audit_axioms GroupApproximation.HullSC.LetterStepBound.or
#audit_axioms GroupApproximation.HullSC.relBall_mapSurjective_subset_of_letterStepBound
#audit_axioms GroupApproximation.HullSC.quotientPeripheralLetterPullbackAt_of_letterStepBound
