import GroupApproximation.Higman.GeneratedPin

/-!
# The value calculus: every one-point set at the origin

`Higman/GeneratedPin.lean` frees every coordinate but the origin, and so turns a
one-point set `{c·e₀}` into the pinned set `{f | f 0 = c}`.  That is the tool
Section 2's constructions are built from, but it takes the one-point set as a
hypothesis.  This module discharges it, for every integer `c` at once.

## The two steps

`S` is the set of sequences `a·e₀ + (a+1)·e₁`, so intersecting it with a pinned
set selects a single member of `S`, and the two liberations then read off either
end of the pair:

* **successor.**  `S ∩ {f | f 0 = c} = {succSeq c}`, whose `τ`-swap is
  `(c+1)·e₀ + c·e₁`; applying `θ` keeps the even coordinates, and since `2i = 1`
  has no integer solution the second track is discarded, leaving `{(c+1)·e₀}`.
* **predecessor.**  `τ` turns the pinned set at the origin into the pinned set at
  `1`, and `S ∩ {f | f 1 = c} = {succSeq (c-1)}`; here `θ` alone suffices, and
  leaves `{(c-1)·e₀}`.

Both steps consume a one-point set and produce its neighbour, so an induction
over `ℤ` starting from `Z = {0}` reaches every `c`.  `θ` is doing the real work
in each: it is the only operation among the nine that *deletes* a coordinate, and
the parity obstruction `2i ≠ 1` is what makes the deletion clean.

## Consequence

`higmanGenerated_pinZero` becomes unconditional, so a coordinate of a generated
set may be pinned to any value — which is what the octuple set of Theorem 3, the
monotone-flag set of the `W` construction, and the anchor `{g | g 3 = 1}` all
require.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

/-- The sequences whose value at coordinate `1` is `c`. -/
def pinOne (c : ℤ) : Set E := {f | f 1 = c}

/-- The transposition of the coordinates `0` and `1`. -/
noncomputable def swap01 (f : E) : E :=
  Finsupp.equivMapDomain (Equiv.swap (0 : ℤ) 1) f

@[simp] theorem swap01_apply (f : E) (i : ℤ) :
    swap01 f i = f (Equiv.swap (0 : ℤ) 1 i) := by
  unfold swap01
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_swap]

/-- `τ` moves the pin from the origin to coordinate `1`. -/
theorem tauOp_pinZero (c : ℤ) : tauOp (pinZero c) = pinOne c := by
  ext f
  constructor
  · rintro ⟨g, hg, _, h1, _⟩
    show f 1 = c
    rw [h1]
    exact hg
  · intro hf
    have hf1 : f 1 = c := hf
    refine ⟨swap01 f, ?_, ?_, ?_, ?_⟩
    · show swap01 f 0 = c
      rw [swap01_apply, Equiv.swap_apply_left, hf1]
    · rw [swap01_apply, Equiv.swap_apply_right]
    · rw [swap01_apply, Equiv.swap_apply_left]
    · intro i hi0 hi1
      rw [swap01_apply, Equiv.swap_apply_of_ne_of_ne hi0 hi1]

/-- Intersecting `S` with a pin at the origin selects one member of `S`. -/
theorem Sset_inter_pinZero (c : ℤ) : Sset ∩ pinZero c = {succSeq c} := by
  ext f
  constructor
  · rintro ⟨⟨a, ha⟩, hp⟩
    have h0 : f 0 = c := hp
    rw [← ha, succSeq_apply_zero] at h0
    rw [← ha, h0]
    rfl
  · intro hf
    have hf' : f = succSeq c := hf
    exact ⟨⟨c, hf'.symm⟩, by rw [hf']; exact succSeq_apply_zero c⟩

/-- Intersecting `S` with a pin at coordinate `1` selects the previous member. -/
theorem Sset_inter_pinOne (c : ℤ) : Sset ∩ pinOne c = {succSeq (c - 1)} := by
  ext f
  constructor
  · rintro ⟨⟨a, ha⟩, hp⟩
    have h1 : f 1 = c := hp
    rw [← ha, succSeq_apply_one] at h1
    have : a = c - 1 := by omega
    rw [← ha, this]
    rfl
  · intro hf
    have hf' : f = succSeq (c - 1) := hf
    refine ⟨⟨c - 1, hf'.symm⟩, ?_⟩
    show f 1 = c
    rw [hf', succSeq_apply_one]
    omega

/-- `θ` deletes the second track of a member of `S`: the parity obstruction
`2i ≠ 1` is what makes it clean. -/
theorem thetaOp_succSeq (c : ℤ) :
    thetaOp {succSeq c} = {Finsupp.single (0 : ℤ) c} := by
  ext f
  constructor
  · rintro ⟨g, hg, h⟩
    have hg' : g = succSeq c := hg
    show f = Finsupp.single (0 : ℤ) c
    ext i
    rw [h i, hg']
    rcases eq_or_ne i 0 with rfl | hi
    · simp [succSeq]
    · have h0 : (2 : ℤ) * i ≠ 0 := by omega
      have h1 : (2 : ℤ) * i ≠ 1 := by omega
      rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
      simp [succSeq, Ne.symm h0, Ne.symm h1]
  · intro hf
    have hf' : f = Finsupp.single (0 : ℤ) c := hf
    refine ⟨succSeq c, rfl, ?_⟩
    intro i
    rw [hf']
    rcases eq_or_ne i 0 with rfl | hi
    · simp [succSeq]
    · have h0 : (2 : ℤ) * i ≠ 0 := by omega
      have h1 : (2 : ℤ) * i ≠ 1 := by omega
      rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
      simp [succSeq, Ne.symm h0, Ne.symm h1]

/-- The same after a `τ`-swap, which reads off the other end of the pair. -/
theorem thetaOp_tauOp_succSeq (c : ℤ) :
    thetaOp (tauOp {succSeq c}) = {Finsupp.single (0 : ℤ) (c + 1)} := by
  ext f
  constructor
  · rintro ⟨g, ⟨g', hg', hgz, _, hgr⟩, h⟩
    have hg'' : g' = succSeq c := hg'
    show f = Finsupp.single (0 : ℤ) (c + 1)
    ext i
    rw [h i]
    rcases eq_or_ne i 0 with rfl | hi
    · rw [mul_zero, hgz, hg'', succSeq_apply_one]
      simp
    · have h0 : (2 : ℤ) * i ≠ 0 := by omega
      have h1 : (2 : ℤ) * i ≠ 1 := by omega
      rw [Finsupp.single_apply, if_neg (Ne.symm hi), hgr _ h0 h1, hg'']
      simp [succSeq, Ne.symm h0, Ne.symm h1]
  · intro hf
    have hf' : f = Finsupp.single (0 : ℤ) (c + 1) := hf
    refine ⟨swap01 (succSeq c), ⟨succSeq c, rfl, ?_, ?_, ?_⟩, ?_⟩
    · rw [swap01_apply, Equiv.swap_apply_left]
    · rw [swap01_apply, Equiv.swap_apply_right]
    · intro i hi0 hi1
      rw [swap01_apply, Equiv.swap_apply_of_ne_of_ne hi0 hi1]
    · intro i
      rw [hf', swap01_apply]
      rcases eq_or_ne i 0 with rfl | hi
      · rw [mul_zero, Equiv.swap_apply_left, succSeq_apply_one]
        simp
      · have h0 : (2 : ℤ) * i ≠ 0 := by omega
        have h1 : (2 : ℤ) * i ≠ 1 := by omega
        rw [Finsupp.single_apply, if_neg (Ne.symm hi),
          Equiv.swap_apply_of_ne_of_ne h0 h1]
        simp [succSeq, Ne.symm h0, Ne.symm h1]

/-! ## The `σ` route, which is what the induction below actually uses

Both steps of the induction need a *bijection of the index set* carrying
coordinate `1` to coordinate `0`: the successor step to bring the second
component of `succSeq c` where `θ` can read it, the predecessor step to turn the
pin at `0` into the pin at `1`.  `τ` does that, and so does the infinite
dihedral group `⟨σ, ρ⟩`, which is already available --- `σ` is
`Higman.ShiftOperation`'s automorphism and `ρ` is proved by
`Higman.ClosuresAssembly.operationClosures_rho`, whereas `τ` is an open leaf of
`OperationClosures` that three impossibility theorems now say is expensive.

So the induction is run on `σ` and the down-shift `ρ σ ρ` instead.  Nothing
about the statements changes; `Seq.tauOp_pinZero` and
`Seq.thetaOp_tauOp_succSeq` above are kept, unused by this file, as the record
of what `τ` would have done.  See `notes/W6_TAU_ROUTE_C_2026-08-22.md`. -/

/-- The down-shift of a sequence: reflect, shift up, reflect back. -/
noncomputable def downOf (f : E) : E := reflect (shiftSeq (reflect f))

@[simp] theorem downOf_apply (f : E) (i : ℤ) : downOf f i = f (i + 1) := by
  unfold downOf
  rw [reflect_apply, shiftSeq_apply, reflect_apply]
  congr 1
  ring

/-- **The down-shift undoes the shift**, which is why `σ` acts on sets by a
bijection and can move a pin. -/
theorem shiftSeq_downOf (f : E) : shiftSeq (downOf f) = f := by
  refine Finsupp.ext fun i => ?_
  rw [shiftSeq_apply, downOf_apply]
  congr 1
  ring

theorem rhoOp_singleton (g : E) : rhoOp ({g} : Set E) = {reflect g} := by
  ext f
  constructor
  · rintro ⟨h, hh, hf⟩
    -- `subst` here would eliminate `g`, the binder of this theorem, rather than
    -- the locally introduced `h`; rewrite pointwise instead.
    have hhg : h = g := hh
    show f = reflect g
    refine Finsupp.ext fun i => ?_
    rw [hf i, hhg, reflect_apply]
  · intro hf
    have hf' : f = reflect g := hf
    exact ⟨g, rfl, fun i => by rw [hf', reflect_apply]⟩

theorem sigmaOp_singleton (g : E) : sigmaOp ({g} : Set E) = {shiftSeq g} := by
  unfold sigmaOp
  rw [Set.image_singleton]

theorem rhoOp_sigmaOp_rhoOp_singleton (g : E) :
    rhoOp (sigmaOp (rhoOp ({g} : Set E))) = {downOf g} := by
  unfold downOf
  rw [rhoOp_singleton, sigmaOp_singleton, rhoOp_singleton]

/-- **`σ` carries the pin at `0` to the pin at `1`.**  The replacement for
`Seq.tauOp_pinZero`: both operations move the pinned coordinate, and this one
costs nothing. -/
theorem sigmaOp_pinZero (c : ℤ) : sigmaOp (pinZero c) = pinOne c := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg0 : g 0 = c := hg
    show shiftSeq g 1 = c
    rw [shiftSeq_apply, show (1 : ℤ) - 1 = 0 from by ring]
    exact hg0
  · intro hf
    have hf1 : f 1 = c := hf
    refine ⟨downOf f, ?_, shiftSeq_downOf f⟩
    show downOf f 0 = c
    rw [downOf_apply, show (0 : ℤ) + 1 = 1 from by ring]
    exact hf1

/-- **The down-shift reads the second component of the pair**, which is the one
thing `τ` was doing in the successor step.  The parity obstruction is the same
as in `thetaOp_succSeq`: `2i + 1` is never `0`, and is `1` only at `i = 0`. -/
theorem thetaOp_rhoOp_sigmaOp_rhoOp_succSeq (c : ℤ) :
    thetaOp (rhoOp (sigmaOp (rhoOp {succSeq c}))) = {Finsupp.single (0 : ℤ) (c + 1)} := by
  rw [rhoOp_sigmaOp_rhoOp_singleton]
  ext f
  constructor
  · rintro ⟨g, hg, h⟩
    have hgd : g = downOf (succSeq c) := hg
    show f = Finsupp.single (0 : ℤ) (c + 1)
    ext i
    rw [h i, hgd, downOf_apply]
    rcases eq_or_ne i 0 with rfl | hi
    · rw [mul_zero, zero_add, succSeq_apply_one]
      simp
    · have h0 : (2 : ℤ) * i + 1 ≠ 0 := by omega
      have h1 : (2 : ℤ) * i + 1 ≠ 1 := by omega
      rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
      simp [succSeq, Ne.symm h0, Ne.symm h1]
  · intro hf
    have hf' : f = Finsupp.single (0 : ℤ) (c + 1) := hf
    refine ⟨downOf (succSeq c), rfl, fun i => ?_⟩
    rw [hf', downOf_apply]
    rcases eq_or_ne i 0 with rfl | hi
    · rw [mul_zero, zero_add, succSeq_apply_one]
      simp
    · have h0 : (2 : ℤ) * i + 1 ≠ 0 := by omega
      have h1 : (2 : ℤ) * i + 1 ≠ 1 := by omega
      rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
      simp [succSeq, Ne.symm h0, Ne.symm h1]

/-! ## The induction -/

/-- **Every one-point set at the origin is generated.**  Induction over `ℤ` from
`Z = {0}`, stepping with `S` and the two liberations. -/
theorem higmanGenerated_singleZero (c : ℤ) :
    HigmanGenerated ({Finsupp.single (0 : ℤ) c} : Set E) := by
  induction c using Int.induction_on with
  | zero =>
      have h : ({Finsupp.single (0 : ℤ) (0 : ℤ)} : Set E) = Zset := by
        rw [Finsupp.single_zero]; rfl
      rw [h]
      exact HigmanGenerated.zero
  | succ n ih =>
      rw [← thetaOp_rhoOp_sigmaOp_rhoOp_succSeq (n : ℤ), ← Sset_inter_pinZero (n : ℤ)]
      exact HigmanGenerated.theta (HigmanGenerated.rho (HigmanGenerated.sigma
        (HigmanGenerated.rho (HigmanGenerated.inter HigmanGenerated.succ
          (higmanGenerated_pinZero (n : ℤ) ih)))))
  | pred n ih =>
      rw [← thetaOp_succSeq ((-(n : ℤ)) - 1),
        show ({succSeq ((-(n : ℤ)) - 1)} : Set E)
            = Sset ∩ pinOne (-(n : ℤ)) from (Sset_inter_pinOne (-(n : ℤ))).symm,
        ← sigmaOp_pinZero (-(n : ℤ))]
      exact HigmanGenerated.theta (HigmanGenerated.inter HigmanGenerated.succ
        (HigmanGenerated.sigma (higmanGenerated_pinZero (-(n : ℤ)) ih)))

/-- **A coordinate may be pinned to any value**, unconditionally. -/
theorem higmanGenerated_pinZero' (c : ℤ) : HigmanGenerated (pinZero c) :=
  higmanGenerated_pinZero c (higmanGenerated_singleZero c)

/-- And at coordinate `1`, by `σ` rather than `τ`. -/
theorem higmanGenerated_pinOne (c : ℤ) : HigmanGenerated (pinOne c) := by
  rw [← sigmaOp_pinZero c]
  exact HigmanGenerated.sigma (higmanGenerated_pinZero' c)

end Seq
end Higman
end GroupApproximation
