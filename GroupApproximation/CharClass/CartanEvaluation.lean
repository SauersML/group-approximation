import GroupApproximation.CharClass.Cartan
import GroupApproximation.CharClass.CartanGroupRing

/-!
# Evaluating the Cartan comparison: the coefficient module and the vanishing
of the `1 + T` term

`Cartan.lean` reduces the Cartan formula to: two natural equivariant chain maps
out of `W ⊗ S(X)` agree in degree `0`, hence the cochains obtained by evaluating
a functional against them differ by an explicit coboundary
(`NaturalHomotopy.cochain_succ`).  Turning that coboundary into a literal `δ` of
a cochain on the space needs one further observation, which is what this file
supplies.

The differential of `W ⊗ S(X)` on the basis element `e_n ⊗ σ` is
`(1 + T)·(e_{n-1} ⊗ σ) + e_n ⊗ ∂σ`.  The evaluating functional takes values in
`ZMod 2` **with the trivial action of the group ring**, and it is `Λ`-linear —
which it must be, since `NaturalHomotopy.cochain_succ` types it as a morphism of
`Λ`-modules.  So it sends `(1 + T)·y` to `v y + T·v y = v y + v y = 2·v y = 0`,
and the whole `(1 + T)` term drops out.  What is left is exactly `δ` of the
cochain `σ ↦ v (e_n ⊗ σ)`, with no leftover term to explain away.

That the coefficient module carries the trivial action is not an extra
assumption: it is forced by the same requirement that makes `u = a ⊗ b ⊗ a ⊗ b`
`Λ`-linear in the first place, namely that `u` be invariant under the block swap
`(13)(24)` of the four tensor factors.  Under the alternative action `(12)(34)`
the functional is not invariant and the evaluation step does not typecheck at
all; see the lane report.

Contents: the general vanishing lemma over any `Λ` with `2 = 0` and any module
on which the chosen involution acts trivially; its "split off the `(1+T)` part"
corollary, in the shape the extraction uses; and the concrete coefficient module
`ZMod 2` over the mod-2 group ring of `ℤ/2`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory

section Vanishing

variable {Λ : Type} [CommRing Λ] (t : Λ)
variable {V R : Type} [AddCommGroup V] [Module Λ V] [AddCommGroup R] [Module Λ R]

/-- **The `1 + T` term dies.**  A `Λ`-linear map into a module on which `t` acts
trivially kills `(1 + t) • x`, because the two summands coincide and `2 = 0`. -/
lemma map_one_add_smul_eq_zero (htriv : ∀ r : R, t • r = r) (h2 : (2 : Λ) = 0)
    (v : V →ₗ[Λ] R) (x : V) : v ((1 + t) • x) = 0 := by
  rw [add_smul, one_smul, map_add, map_smul, htriv, ← two_smul Λ (v x), h2, zero_smul]

/-- The form in which the vanishing is used: only the part of the differential
that does not carry the factor `1 + t` contributes. -/
lemma map_eq_of_split (htriv : ∀ r : R, t • r = r) (h2 : (2 : Λ) = 0)
    (v : V →ₗ[Λ] R) {w y z : V} (hw : w = (1 + t) • y + z) : v w = v z := by
  rw [hw, map_add, map_one_add_smul_eq_zero t htriv h2 v y, zero_add]

end Vanishing

section Coefficients

/-- **The vanishing at the concrete group ring.**  Only the triviality of the
action on the coefficients has to be supplied; characteristic two is a fact
about `(ZMod 2)[ℤ/2]` itself. -/
lemma map_one_add_gen_eq_zero {V R : Type} [AddCommGroup V] [Module GroupRingZ2 V]
    [AddCommGroup R] [Module GroupRingZ2 R] (htriv : ∀ r : R, groupRingGen • r = r)
    (v : V →ₗ[GroupRingZ2] R) (x : V) : v ((1 + groupRingGen) • x) = 0 :=
  map_one_add_smul_eq_zero groupRingGen htriv two_eq_zero_groupRingZ2 v x

/-- Only the part of the source differential that does not carry the factor
`1 + T` contributes to the coboundary. -/
lemma map_eq_of_split_gen {V R : Type} [AddCommGroup V] [Module GroupRingZ2 V]
    [AddCommGroup R] [Module GroupRingZ2 R] (htriv : ∀ r : R, groupRingGen • r = r)
    (v : V →ₗ[GroupRingZ2] R) {w y z : V} (hw : w = (1 + groupRingGen) • y + z) :
    v w = v z :=
  map_eq_of_split groupRingGen htriv two_eq_zero_groupRingZ2 v hw

/-- **The coefficient module of the evaluation**: `ZMod 2` over the mod-2 group
ring of `ℤ/2`, with the generator acting as the identity.  This is the target of
the functional `a ⊗ b ⊗ a ⊗ b`, and the trivial action is what makes that
functional `Λ`-linear. -/
noncomputable abbrev trivialCoeff : Module GroupRingZ2 (ZMod 2) :=
  moduleOfInvolution (1 : Module.End (ZMod 2) (ZMod 2)) (one_mul 1)

/-- The generator of the group ring acts trivially on the coefficient module,
which is the hypothesis `map_one_add_gen_eq_zero` needs. -/
lemma trivialCoeff_gen_smul (r : ZMod 2) :
    letI := trivialCoeff
    groupRingGen • r = r := by
  letI := trivialCoeff
  rw [moduleOfInvolution_smul]
  rfl

end Coefficients

/-! ## The comparison, evaluated -/

section Evaluated

universe u v w

variable {C : Type u} [Category.{v} C] {ι : Type w} {M : ι → C}
variable {Λ : Type} [CommRing Λ]
variable {F G : C ⥤ ChainComplex (ModuleCat.{0} Λ) ℕ}

/-- **The internal Cartan comparison, evaluated.**

This is the exact shape the final extraction uses.  `u` is the evaluating
functional (in the application, `a ⊗ b ⊗ a ⊗ b` for a pair of cocycles), which
must annihilate boundaries and be `Λ`-linear — the latter is why the action on
the fourfold tensor has to be the block swap.  `x` is a basis element of the
source, `e_n ⊗ σ`, whose differential splits as `(1 + t)·(e_{n-1} ⊗ σ)` plus the
term `z = e_n ⊗ ∂σ`.  The conclusion says the two evaluations differ by `v z`
alone: the `(1 + t)` half of the differential contributes nothing, because `v`
is `Λ`-linear into a module with trivial action and `2 = 0`.  So the difference
of the two cochains is literally `δ` of `σ ↦ v (e_n ⊗ σ)`. -/
theorem DiagonalComparison.eval_sub_eq (D : DiagonalComparison M Λ F G) (X : C) (n : ℕ)
    {R : ModuleCat.{0} Λ} (u : (G.obj X).X (n + 1) ⟶ R)
    (hu : (G.obj X).d (n + 2) (n + 1) ≫ u = 0)
    (t : Λ) (htriv : ∀ r : R, t • r = r) (h2 : (2 : Λ) = 0)
    (x : (F.obj X).X (n + 1)) (y z : (F.obj X).X n)
    (hx : ((F.obj X).d (n + 1) n).hom x = (1 + t) • y + z) :
    ((D.Φ₁.app X).f (n + 1) ≫ u).hom x
      = ((D.Φ₂.app X).f (n + 1) ≫ u).hom x + (D.homotopy.s n X ≫ u).hom z := by
  have hco := D.homotopy.cochain_succ X n u hu
  -- Both reassociations below are definitional for `ModuleCat` morphisms.
  have happ : ((D.Φ₁.app X).f (n + 1) ≫ u).hom x
      = ((D.Φ₂.app X).f (n + 1) ≫ u).hom x
        + ((F.obj X).d (n + 1) n ≫ (D.homotopy.s n X ≫ u)).hom x :=
    congrArg (fun w : (F.obj X).X (n + 1) ⟶ R => w.hom x) hco
  have hsplit : ((F.obj X).d (n + 1) n ≫ (D.homotopy.s n X ≫ u)).hom x
      = (D.homotopy.s n X ≫ u).hom z := by
    have h1 : ((F.obj X).d (n + 1) n ≫ (D.homotopy.s n X ≫ u)).hom x
        = (D.homotopy.s n X ≫ u).hom (((F.obj X).d (n + 1) n).hom x) := rfl
    rw [h1, hx]
    exact map_eq_of_split t htriv h2 (D.homotopy.s n X ≫ u).hom rfl
  rw [happ, hsplit]

end Evaluated

end GroupApproximation.CharClass
