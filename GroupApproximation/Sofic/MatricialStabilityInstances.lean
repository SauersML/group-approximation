import GroupApproximation.Sofic.FreeGroupResiduallyFinite
import GroupApproximation.Sofic.LEF
import GroupApproximation.Sofic.LocallyFiniteMF
import GroupApproximation.Sofic.MatricialStabilityRadical
import GroupApproximation.Sofic.OperatorMFPositiveControls

/-!
# Groups that are point-norm matricially stable

`MatricialStabilityRadical.IsPointNormMatriciallyStable` is the hypothesis of
clauses 2 and 3 of `prop:stabradical`.  It is a predicate this development
defines and, until this file, one that no theorem of this development ever
concludes: the two clauses were true statements about an empty class.  This
file gives the predicate its first inhabitants -- every free group, and the
integers -- and then instantiates both clauses at them.

## What the predicate asks for

Point-norm matricial stability asks that every operator-norm almost
representation `B` admit genuine finite-dimensional unitary representations
`pi n`, **on the very models `B` already uses**, with

`‖B.map n g - pi n g‖ → 0` for each fixed `g`.

The thresholds may depend on `g` and on the tolerance; no uniformity over the
group is asked for, and none is proved.

## The route: free groups need no repair

For a free group nothing has to be corrected.  A homomorphism out of a free
group may be prescribed arbitrarily on the generators, so
`pi n := FreeGroup.lift (fun a ↦ B.map n (FreeGroup.of a))` matches `B`
*exactly* at every generator, and the only question is whether the match
survives the group operations.  It does, and the reason is that the operator
norm on a matrix algebra is bi-invariant under unitaries, which makes the error
of a product *additive* rather than multiplicative: for unitaries,

`‖xy - x'y'‖ ≤ ‖xy - x'y‖ + ‖x'y - x'y'‖`, and the right side is
`‖x - x'‖ + ‖y - y'‖`.

So the set of elements at which `pi` tracks `B` is closed under products.  It
is closed under inverses because `‖u⁻¹ - v⁻¹‖ = ‖u - v‖` for unitaries and
because `B.map n x * B.map n x⁻¹` tends to `1`, and it contains `1` because a
unitary `u` with `u ≈ u * u` satisfies `‖u - 1‖ = ‖u - u * u‖`.  It is
therefore a subgroup (`matchLocus`), and a subgroup of a free group with all the
generators is the whole group.  A fixed group element is a fixed word, so only
finitely many thresholds are combined and a common bound always exists.

`Multiplicative ℤ` is handled by the same subgroup, generated this time by a
single element, with `pi n` the power homomorphism attached to
`B.map n (Multiplicative.ofAdd 1)`.

## Why these targets and not stronger ones

* **Finite groups** are matricially stable -- the classical averaging argument
  compares the almost representation with the regular representation on `H^G`
  through the exact isometry `ξ ↦ |G|^(-1/2) (u_g ξ)_g`, averages the
  resulting projection over `G`, and repairs what is left.  That argument is not
  word-combinatorial: the averaged projection is only an approximate
  projection, so it has to be *rounded* by a spectral-gap functional calculus,
  and the rounded projection then has to be transported by the unitary
  equivalence of two projections at distance less than one.  Neither ingredient
  exists at the matrix level in this repository, and neither is short.  Nothing
  here contradicts the stability of finite groups; it is simply not proved here,
  and this file does not assert it.
* **Amenable groups** (Hadwin--Shulman, Eckhardt--Shulman style theorems) are
  literature.  They are not cited and not used: every declaration below is
  proved from the definitions.
* `Multiplicative ℤ` is recorded separately from `FreeGroup Unit` because the
  corollaries attach to this repository's own `isLEF_multiplicative_int`, and
  because it is the concrete finitely generated abelian witness.

## What the instances buy, stated exactly

Clause 2 (`actualCoronaMFResidual_eq_fdUnitaryResidual`) becomes a statement
about concrete groups: at a free group and at the integers, the literal
genuine-corona MF radical *is* the intersection of the kernels of all
finite-dimensional unitary representations.

Clause 3 (`not_isCDEOperatorMF_of_stable_of_fdResidual_ne_bot`) is different in
kind, and the difference should be said plainly.  Its two hypotheses are jointly
satisfiable only by a group that is not MF, since that is exactly what the
clause concludes.  No example can therefore make clause 3 fire without
exhibiting a non-MF group by this route, and the honest instantiation is the
contrapositive: at a stable group that *is* MF, clause 3 forces the
finite-dimensional residual to vanish.  That is what
`freeGroup_fdUnitaryResidual_eq_bot` and
`multiplicativeInt_fdUnitaryResidual_eq_bot` record, and it is a real
consequence -- residual finite dimensionality -- deduced through the clause
rather than a restatement of it.

No declaration in this file takes a section `variable`; every binder is printed
in the header of the declaration that uses it.
-/

namespace GroupApproximation
namespace MatricialStabilityInstances

open MatricialStabilityRadical
open scoped Matrix
open scoped Matrix.Norms.L2Operator

universe u

/-! ## Unitary bookkeeping in the operator norm -/

/-- The coordinates of a product of unitaries are the product of the
coordinates. -/
@[simp] theorem coe_unitary_mul (Y : FiniteModel) (u v : Matrix.unitaryGroup Y ℂ) :
    ((u * v : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) =
      (u : Matrix Y Y ℂ) * (v : Matrix Y Y ℂ) := rfl

/-- The coordinates of an inverse unitary are the conjugate transpose. -/
theorem coe_unitary_inv (Y : FiniteModel) (u : Matrix.unitaryGroup Y ℂ) :
    ((u⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) =
      (u : Matrix Y Y ℂ)ᴴ := by
  rw [← Matrix.star_eq_conjTranspose]
  rfl

/-- Insert an intermediate point in a norm estimate. -/
theorem norm_sub_le_add_norm_sub {A : Type*} [SeminormedAddCommGroup A]
    (a b c : A) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc ‖a - c‖ = ‖(a - b) + (b - c)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖a - b‖ + ‖b - c‖ := norm_add_le _ _

/-- **Unitary inversion is an isometry.**  Inversion is the adjoint on
unitaries, and the adjoint preserves the operator norm. -/
theorem norm_inv_sub_inv (Y : FiniteModel) (u v : Matrix.unitaryGroup Y ℂ) :
    ‖((u⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) -
        ((v⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ)‖ =
      ‖(u : Matrix Y Y ℂ) - (v : Matrix Y Y ℂ)‖ := by
  rw [coe_unitary_inv, coe_unitary_inv]
  have hsub : (u : Matrix Y Y ℂ)ᴴ - (v : Matrix Y Y ℂ)ᴴ =
      ((u : Matrix Y Y ℂ) - (v : Matrix Y Y ℂ))ᴴ := by
    simp
  rw [hsub, ← Matrix.star_eq_conjTranspose, norm_star]

/-- **The error of a product of unitaries is additive.**  This is the whole
mechanism behind the free-group case: bi-invariance of the operator norm
prevents the two errors from amplifying each other. -/
theorem norm_mul_sub_mul_le (Y : FiniteModel)
    (a b c d : Matrix.unitaryGroup Y ℂ) :
    ‖(a : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ) -
        (b : Matrix Y Y ℂ) * (d : Matrix Y Y ℂ)‖ ≤
      ‖(a : Matrix Y Y ℂ) - (b : Matrix Y Y ℂ)‖ +
        ‖(c : Matrix Y Y ℂ) - (d : Matrix Y Y ℂ)‖ := by
  have h1 : ‖(a : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ) -
      (b : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ)‖ =
      ‖(a : Matrix Y Y ℂ) - (b : Matrix Y Y ℂ)‖ := by
    rw [← Matrix.sub_mul, CStarRing.norm_mul_mem_unitary _ c.2]
  have h2 : ‖(b : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ) -
      (b : Matrix Y Y ℂ) * (d : Matrix Y Y ℂ)‖ =
      ‖(c : Matrix Y Y ℂ) - (d : Matrix Y Y ℂ)‖ := by
    rw [← Matrix.mul_sub, CStarRing.norm_mem_unitary_mul _ b.2]
  calc ‖(a : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ) -
        (b : Matrix Y Y ℂ) * (d : Matrix Y Y ℂ)‖ ≤
      ‖(a : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ) -
          (b : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ)‖ +
        ‖(b : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ) -
          (b : Matrix Y Y ℂ) * (d : Matrix Y Y ℂ)‖ :=
      norm_sub_le_add_norm_sub _ _ _
    _ = ‖(a : Matrix Y Y ℂ) - (b : Matrix Y Y ℂ)‖ +
        ‖(c : Matrix Y Y ℂ) - (d : Matrix Y Y ℂ)‖ := by rw [h1, h2]

/-! ## Two asymptotic facts about an almost representation -/

/-- **An almost representation is asymptotically unital.**  A unitary `u` with
`u` close to `u * u` is close to `1`, because `u - u * u = u * (1 - u)` and `u`
is an isometry. -/
theorem eventually_norm_map_one_sub_one_le {G : Type u} [Group G]
    (B : OpAlmostRepresentation G) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N,
      ‖(B.map n 1 : Matrix (B.model n) (B.model n) ℂ) - 1‖ ≤ ε := by
  obtain ⟨N, hN⟩ := B.asymptoticallyMultiplicative 1 1 ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have h := hN n hn
  rw [one_mul (1 : G)] at h
  have hfac : (B.map n 1 : Matrix (B.model n) (B.model n) ℂ) -
      (B.map n 1 : Matrix (B.model n) (B.model n) ℂ) *
        (B.map n 1 : Matrix (B.model n) (B.model n) ℂ) =
      (B.map n 1 : Matrix (B.model n) (B.model n) ℂ) *
        (1 - (B.map n 1 : Matrix (B.model n) (B.model n) ℂ)) := by
    rw [Matrix.mul_sub, Matrix.mul_one]
  rw [hfac, CStarRing.norm_mem_unitary_mul _ (B.map n 1).2] at h
  rwa [norm_sub_rev] at h

/-- **An almost representation is asymptotically inverse preserving.**  Its
value at `x⁻¹` converges to the genuine inverse of its value at `x`. -/
theorem eventually_norm_map_inv_sub_inv_le {G : Type u} [Group G]
    (B : OpAlmostRepresentation G) (x : G) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N,
      ‖(B.map n x⁻¹ : Matrix (B.model n) (B.model n) ℂ) -
        (((B.map n x)⁻¹ : Matrix.unitaryGroup (B.model n) ℂ) :
          Matrix (B.model n) (B.model n) ℂ)‖ ≤ ε := by
  obtain ⟨N1, h1⟩ :=
    B.asymptoticallyMultiplicative x x⁻¹ (ε / 2) (by linarith)
  obtain ⟨N2, h2⟩ := eventually_norm_map_one_sub_one_le B
    (ε := ε / 2) (by linarith)
  refine ⟨max N1 N2, fun n hn ↦ ?_⟩
  have hA := h1 n (le_trans (le_max_left _ _) hn)
  have hB := h2 n (le_trans (le_max_right _ _) hn)
  rw [mul_inv_cancel x] at hA
  have hcancel : (B.map n x : Matrix (B.model n) (B.model n) ℂ) *
      (((B.map n x)⁻¹ : Matrix.unitaryGroup (B.model n) ℂ) :
        Matrix (B.model n) (B.model n) ℂ) = 1 :=
    congrArg Subtype.val (mul_inv_cancel (B.map n x))
  have hsplit : (B.map n x : Matrix (B.model n) (B.model n) ℂ) *
      (B.map n x⁻¹ : Matrix (B.model n) (B.model n) ℂ) - 1 =
      (B.map n x : Matrix (B.model n) (B.model n) ℂ) *
        ((B.map n x⁻¹ : Matrix (B.model n) (B.model n) ℂ) -
          (((B.map n x)⁻¹ : Matrix.unitaryGroup (B.model n) ℂ) :
            Matrix (B.model n) (B.model n) ℂ)) := by
    rw [Matrix.mul_sub, hcancel]
  have hkey : ‖(B.map n x⁻¹ : Matrix (B.model n) (B.model n) ℂ) -
      (((B.map n x)⁻¹ : Matrix.unitaryGroup (B.model n) ℂ) :
        Matrix (B.model n) (B.model n) ℂ)‖ =
      ‖(B.map n x : Matrix (B.model n) (B.model n) ℂ) *
        (B.map n x⁻¹ : Matrix (B.model n) (B.model n) ℂ) - 1‖ := by
    rw [hsplit, CStarRing.norm_mem_unitary_mul _ (B.map n x).2]
  rw [hkey]
  calc ‖(B.map n x : Matrix (B.model n) (B.model n) ℂ) *
        (B.map n x⁻¹ : Matrix (B.model n) (B.model n) ℂ) - 1‖ ≤
      ‖(B.map n x : Matrix (B.model n) (B.model n) ℂ) *
          (B.map n x⁻¹ : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n 1 : Matrix (B.model n) (B.model n) ℂ)‖ +
        ‖(B.map n 1 : Matrix (B.model n) (B.model n) ℂ) - 1‖ :=
      norm_sub_le_add_norm_sub _ _ _
    _ ≤ ε / 2 + ε / 2 := by
        refine add_le_add ?_ hB
        rwa [norm_sub_rev]
    _ = ε := by ring

/-! ## The locus where a genuine sequence tracks an almost representation -/

/-- The elements at which a sequence of genuine finite-dimensional unitary
representations tracks an operator-norm almost representation. -/
def AsymptoticallyMatches {G : Type u} [Group G] (B : OpAlmostRepresentation G)
    (pi : ∀ n, G →* Matrix.unitaryGroup (B.model n) ℂ) (g : G) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
    ‖(B.map n g : Matrix (B.model n) (B.model n) ℂ) -
      (pi n g : Matrix (B.model n) (B.model n) ℂ)‖ ≤ ε

/-- Every genuine sequence tracks every almost representation at the
identity. -/
theorem asymptoticallyMatches_one {G : Type u} [Group G]
    (B : OpAlmostRepresentation G)
    (pi : ∀ n, G →* Matrix.unitaryGroup (B.model n) ℂ) :
    AsymptoticallyMatches B pi 1 := by
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_norm_map_one_sub_one_le B hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have hone : ((pi n 1 : Matrix.unitaryGroup (B.model n) ℂ) :
      Matrix (B.model n) (B.model n) ℂ) = 1 := by simp
  rw [hone]
  exact hN n hn

/-- Tracking is preserved by products: the two errors add. -/
theorem AsymptoticallyMatches.mul {G : Type u} [Group G]
    {B : OpAlmostRepresentation G}
    {pi : ∀ n, G →* Matrix.unitaryGroup (B.model n) ℂ} {x y : G}
    (hx : AsymptoticallyMatches B pi x) (hy : AsymptoticallyMatches B pi y) :
    AsymptoticallyMatches B pi (x * y) := by
  intro ε hε
  obtain ⟨N1, h1⟩ := hx (ε / 3) (by linarith)
  obtain ⟨N2, h2⟩ := hy (ε / 3) (by linarith)
  obtain ⟨N3, h3⟩ :=
    B.asymptoticallyMultiplicative x y (ε / 3) (by linarith)
  refine ⟨max N1 (max N2 N3), fun n hn ↦ ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N2 ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : N3 ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  rw [map_mul (pi n) x y, coe_unitary_mul]
  calc ‖(B.map n (x * y) : Matrix (B.model n) (B.model n) ℂ) -
        (pi n x : Matrix (B.model n) (B.model n) ℂ) *
          (pi n y : Matrix (B.model n) (B.model n) ℂ)‖ ≤
      ‖(B.map n (x * y) : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n x : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n y : Matrix (B.model n) (B.model n) ℂ)‖ +
        ‖(B.map n x : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n y : Matrix (B.model n) (B.model n) ℂ) -
          (pi n x : Matrix (B.model n) (B.model n) ℂ) *
            (pi n y : Matrix (B.model n) (B.model n) ℂ)‖ :=
      norm_sub_le_add_norm_sub _ _ _
    _ ≤ ε / 3 + (ε / 3 + ε / 3) :=
      add_le_add (h3 n hn3)
        ((norm_mul_sub_mul_le (B.model n) (B.map n x) (pi n x) (B.map n y)
          (pi n y)).trans (add_le_add (h1 n hn1) (h2 n hn2)))
    _ = ε := by ring

/-- Tracking is preserved by inversion: unitary inversion is an isometry, and
the almost representation is asymptotically inverse preserving. -/
theorem AsymptoticallyMatches.inv {G : Type u} [Group G]
    {B : OpAlmostRepresentation G}
    {pi : ∀ n, G →* Matrix.unitaryGroup (B.model n) ℂ} {x : G}
    (hx : AsymptoticallyMatches B pi x) :
    AsymptoticallyMatches B pi x⁻¹ := by
  intro ε hε
  obtain ⟨N1, h1⟩ := hx (ε / 2) (by linarith)
  obtain ⟨N2, h2⟩ := eventually_norm_map_inv_sub_inv_le B x
    (ε := ε / 2) (by linarith)
  refine ⟨max N1 N2, fun n hn ↦ ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N2 ≤ n := le_trans (le_max_right _ _) hn
  rw [map_inv (pi n) x]
  calc ‖(B.map n x⁻¹ : Matrix (B.model n) (B.model n) ℂ) -
        (((pi n x)⁻¹ : Matrix.unitaryGroup (B.model n) ℂ) :
          Matrix (B.model n) (B.model n) ℂ)‖ ≤
      ‖(B.map n x⁻¹ : Matrix (B.model n) (B.model n) ℂ) -
          (((B.map n x)⁻¹ : Matrix.unitaryGroup (B.model n) ℂ) :
            Matrix (B.model n) (B.model n) ℂ)‖ +
        ‖(((B.map n x)⁻¹ : Matrix.unitaryGroup (B.model n) ℂ) :
            Matrix (B.model n) (B.model n) ℂ) -
          (((pi n x)⁻¹ : Matrix.unitaryGroup (B.model n) ℂ) :
            Matrix (B.model n) (B.model n) ℂ)‖ :=
      norm_sub_le_add_norm_sub _ _ _
    _ ≤ ε / 2 + ε / 2 := by
        refine add_le_add (h2 n hn2) ?_
        rw [norm_inv_sub_inv]
        exact h1 n hn1
    _ = ε := by ring

/-- **The tracking locus is a subgroup.**  This is the structural content of
the file: matching a genuine representation asymptotically is a condition
closed under the group operations, so it need only be checked on
generators. -/
def matchLocus {G : Type u} [Group G] (B : OpAlmostRepresentation G)
    (pi : ∀ n, G →* Matrix.unitaryGroup (B.model n) ℂ) : Subgroup G where
  carrier := {g | AsymptoticallyMatches B pi g}
  one_mem' := asymptoticallyMatches_one B pi
  mul_mem' := fun hx hy ↦ hx.mul hy
  inv_mem' := fun hx ↦ hx.inv

@[simp] theorem mem_matchLocus {G : Type u} [Group G]
    {B : OpAlmostRepresentation G}
    {pi : ∀ n, G →* Matrix.unitaryGroup (B.model n) ℂ} {g : G} :
    g ∈ matchLocus B pi ↔ AsymptoticallyMatches B pi g := Iff.rfl

/-- Tracking on a generating set is tracking everywhere. -/
theorem asymptoticallyMatches_of_closure_eq_top {G : Type u} [Group G]
    (B : OpAlmostRepresentation G)
    (pi : ∀ n, G →* Matrix.unitaryGroup (B.model n) ℂ) (S : Set G)
    (hS : Subgroup.closure S = ⊤)
    (hgen : ∀ s ∈ S, AsymptoticallyMatches B pi s) (g : G) :
    AsymptoticallyMatches B pi g := by
  have hle : Subgroup.closure S ≤ matchLocus B pi :=
    (Subgroup.closure_le _).mpr fun s hs ↦ hgen s hs
  rw [hS] at hle
  exact hle (Subgroup.mem_top g)

/-! ## Free groups -/

/-- **Every free group is point-norm matricially stable.**  The genuine
representations are the ones freely determined by the almost representation's
own values at the generators; the estimate then propagates along words because
the operator norm is bi-invariant under unitaries.  No repair, no averaging and
no functional calculus is involved. -/
theorem freeGroup_isPointNormMatriciallyStable :
    ∀ α : Type u, IsPointNormMatriciallyStable (FreeGroup α) := by
  intro α B
  refine ⟨fun n ↦ FreeGroup.lift fun a ↦ B.map n (FreeGroup.of a),
    fun g ↦ ?_⟩
  refine FreeGroup.induction_on g ?_ ?_ ?_ ?_
  · exact asymptoticallyMatches_one B _
  · intro a ε hε
    refine ⟨0, fun n _ ↦ ?_⟩
    simp only [FreeGroup.lift_apply_of, sub_self, norm_zero]
    exact hε.le
  · intro a ha
    exact AsymptoticallyMatches.inv ha
  · intro x y hx hy
    exact AsymptoticallyMatches.mul hx hy

/-! ## The integers -/

/-- The homomorphism out of the multiplicative integers determined by the image
of the generator. -/
def intPowerHom {M : Type*} [Group M] (u : M) : Multiplicative ℤ →* M where
  toFun k := u ^ (Multiplicative.toAdd k)
  map_one' := by simp
  map_mul' a b := by simp [zpow_add]

@[simp] theorem intPowerHom_apply {M : Type*} [Group M] (u : M)
    (k : Multiplicative ℤ) :
    intPowerHom u k = u ^ (Multiplicative.toAdd k) := rfl

/-- **The integers are point-norm matricially stable.**  A single near-unitary
determines a genuine representation of `ℤ` by taking its exact powers, and the
tracking locus, being a subgroup containing the generator, is everything.  No
spectral rounding of the near-unitary is needed: `ℤ` is free, so its
representations are unconstrained. -/
theorem multiplicativeInt_isPointNormMatriciallyStable :
    IsPointNormMatriciallyStable (Multiplicative ℤ) := by
  intro B
  refine ⟨fun n ↦ intPowerHom (B.map n (Multiplicative.ofAdd 1)),
    fun g ↦ ?_⟩
  have hgen : AsymptoticallyMatches B
      (fun n ↦ intPowerHom (B.map n (Multiplicative.ofAdd 1)))
      (Multiplicative.ofAdd (1 : ℤ)) := by
    intro ε hε
    refine ⟨0, fun n _ ↦ ?_⟩
    simp only [intPowerHom_apply, toAdd_ofAdd, zpow_one, sub_self, norm_zero]
    exact hε.le
  have hmem : Multiplicative.ofAdd (1 : ℤ) ∈
      matchLocus B (fun n ↦ intPowerHom (B.map n (Multiplicative.ofAdd 1))) :=
    mem_matchLocus.mpr hgen
  have key : ∀ k : ℤ, Multiplicative.ofAdd k ∈
      matchLocus B
        (fun n ↦ intPowerHom (B.map n (Multiplicative.ofAdd 1))) := by
    intro k
    refine Int.induction_on k ?_ ?_ ?_
    · rw [ofAdd_zero]
      exact Subgroup.one_mem _
    · intro i ih
      rw [ofAdd_add]
      exact Subgroup.mul_mem _ ih hmem
    · intro i ih
      rw [sub_eq_add_neg, ofAdd_add, ofAdd_neg (1 : ℤ)]
      exact Subgroup.mul_mem _ ih (Subgroup.inv_mem _ hmem)
  have hk := key (Multiplicative.toAdd g)
  rw [ofAdd_toAdd] at hk
  exact mem_matchLocus.mp hk

/-! ## The two clauses, instantiated -/

/-- Free groups on a countable alphabet are countable. -/
theorem freeGroupCountable {α : Type u} [Countable α] :
    Countable (FreeGroup α) := by
  have hsurj : Function.Surjective
      (FreeGroup.mk : List (α × Bool) → FreeGroup α) := by
    intro g
    obtain ⟨L, hL⟩ := Quot.exists_rep g
    exact ⟨L, by rw [← FreeGroup.quot_mk_eq_mk, hL]⟩
  exact hsurj.countable

/-- **Clause 2 of `prop:stabradical` at a free group.**  The literal
genuine-corona MF radical of a countable free group is exactly the intersection
of the kernels of its finite-dimensional unitary representations. -/
theorem freeGroup_actualCoronaMFResidual_eq_fdUnitaryResidual :
    ∀ (α : Type u) [Countable α],
      actualCoronaMFResidual (FreeGroup α) =
        fdUnitaryResidual (FreeGroup α) := by
  intro α _
  letI : Countable (FreeGroup α) := freeGroupCountable
  exact MatricialStabilityRadical.actualCoronaMFResidual_eq_fdUnitaryResidual
    (freeGroup_isPointNormMatriciallyStable α)

/-- **Clause 3 of `prop:stabradical` at a free group.**  A countable free group
is MF and is matricially stable, so clause 3 forbids a nontrivial
finite-dimensional residual: free groups are residually finite dimensional. -/
theorem freeGroup_fdUnitaryResidual_eq_bot :
    ∀ (α : Type u) [Countable α],
      fdUnitaryResidual (FreeGroup α) = ⊥ := by
  intro α _
  letI : Countable (FreeGroup α) := freeGroupCountable
  by_contra hne
  exact
    MatricialStabilityRadical.not_isCDEOperatorMF_of_stable_of_fdResidual_ne_bot
      (freeGroup_isPointNormMatriciallyStable α) hne
      ((isCDEOperatorMF_iff_isOperatorMF (FreeGroup α)).mpr
        isOperatorMF_of_residuallyFinite)

/-- The MF radical of a countable free group is trivial, computed through the
finite-dimensional residual rather than through the corona directly. -/
theorem freeGroup_actualCoronaMFResidual_eq_bot :
    ∀ (α : Type u) [Countable α],
      actualCoronaMFResidual (FreeGroup α) = ⊥ := by
  intro α _
  rw [freeGroup_actualCoronaMFResidual_eq_fdUnitaryResidual α,
    freeGroup_fdUnitaryResidual_eq_bot α]

/-- **Clause 2 of `prop:stabradical` at the integers.** -/
theorem multiplicativeInt_actualCoronaMFResidual_eq_fdUnitaryResidual :
    actualCoronaMFResidual (Multiplicative ℤ) =
      fdUnitaryResidual (Multiplicative ℤ) := by
  letI : Countable (Multiplicative ℤ) :=
    Countable.of_equiv ℤ Multiplicative.toAdd
  exact MatricialStabilityRadical.actualCoronaMFResidual_eq_fdUnitaryResidual
    multiplicativeInt_isPointNormMatriciallyStable

/-- **Clause 3 of `prop:stabradical` at the integers.**  The integers are LEF,
hence MF, and matricially stable, so their finite-dimensional residual
vanishes. -/
theorem multiplicativeInt_fdUnitaryResidual_eq_bot :
    fdUnitaryResidual (Multiplicative ℤ) = ⊥ := by
  letI : Countable (Multiplicative ℤ) :=
    Countable.of_equiv ℤ Multiplicative.toAdd
  by_contra hne
  exact
    MatricialStabilityRadical.not_isCDEOperatorMF_of_stable_of_fdResidual_ne_bot
      multiplicativeInt_isPointNormMatriciallyStable hne
      ((isCDEOperatorMF_iff_isOperatorMF (Multiplicative ℤ)).mpr
        (isOperatorMF_of_isLEF isLEF_multiplicative_int))

/-- **The stability hypothesis of `prop:stabradical` is inhabited, and both
clauses have consequences at an inhabitant.**  Recorded as one statement so
that the inventory row tracking this dependence can be closed by pointing at a
single name. -/
theorem stabilityHypothesis_inhabited :
    IsPointNormMatriciallyStable (Multiplicative ℤ) ∧
      actualCoronaMFResidual (Multiplicative ℤ) =
        fdUnitaryResidual (Multiplicative ℤ) ∧
      fdUnitaryResidual (Multiplicative ℤ) = ⊥ :=
  ⟨multiplicativeInt_isPointNormMatriciallyStable,
    multiplicativeInt_actualCoronaMFResidual_eq_fdUnitaryResidual,
    multiplicativeInt_fdUnitaryResidual_eq_bot⟩

end MatricialStabilityInstances
end GroupApproximation
