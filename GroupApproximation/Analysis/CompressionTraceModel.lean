import GroupApproximation.Analysis.ReducedGroupCStarSpan
import GroupApproximation.Analysis.TikuisisWhiteWinter
import GroupApproximation.Analysis.UCPContractiveMatrix

/-!
# Compression models of the canonical trace: everything except multiplicativity

`Analysis.QuasidiagonalTrace` states the conclusion of Tikuisis--White--Winter
--- *the trace is quasidiagonal* --- and `Analysis.TikuisisWhiteWinter` walks
the distance from that conclusion to the printed group implication.  Neither
file constructs a single `QuasidiagonalTraceModel` at a nontrivial algebra,
and the docstring of the first says so.  This file constructs the only family
of candidates a group supplies by elementary means:

> compress to finitely many point masses.

Fix a group `G`, a number `k` and an injective tuple `e : Fin k → G` --- an
enumeration of a `k`-element subset `F ⊆ G` --- and send an operator
`a ∈ C⋆_r(G)` to the `k × k` matrix of its coefficients against the
corresponding point masses:

```text
    φ_e(a)_{pq}  =  ⟪δ_{e p}, a δ_{e q}⟫ .
```

That is `compressionMap e`.  Four of the five clauses of
`Quasidiagonal.QuasidiagonalTraceModel` are proved here, for **every** `e`,
with no hypothesis on `G` at all:

| clause | here |
|---|---|
| `map` is `ℂ`-linear | `compressionMap`, by construction |
| `map_one` | `compressionMap_one` --- needs injectivity of `e`, and nothing else |
| `completelyPositive` | `isCompletelyPositiveOnMatrices_compressionMap` --- the form is `‖∑ᵢ aᵢ vᵢ‖²` |
| `tendsto_trace` | `normTrace_compressionMap` --- **an equality, not a limit** |

The trace clause deserves a second look.  For a compression it is not an
asymptotic statement and involves no Følner condition: the normalized trace of
`φ_e(a)` is `τ(a)` **exactly**, for every `a` and every `e`, because the
canonical trace is invariant under conjugation by the *right* translations
(`inner_pointMass_apply`) and the point masses form a single right-translation
orbit.  So all the analytic content of quasidiagonality, for this family of
candidates, sits in the one remaining clause:

```text
    ‖φ_e(ab) − φ_e(a) φ_e(b)‖ → 0     (operator norm).
```

`Analysis.CompressionTraceRigidity` computes that defect exactly --- it is `0`
or at least `1`, never small --- and
`Analysis.CompressionTraceLocallyFinite` identifies the groups that can make
it vanish.  What is proved here is what those two files consume, plus the
packaging `CompressionFamily` in which the route is stated.

## What this file is not

It is **not** a proof of Tikuisis--White--Winter, and no theorem here is
conditional on one.  It is the elementary part of one, made explicit so that
the non-elementary part can be located exactly.

## Manuscript status

Infrastructure for `INT.11`/`CY.12c`; certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace Quasidiagonal

open Filter ReducedGroupCStarTrace
open scoped InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- The point-mass lemmas quantify over a decidable equality on the group.
This is the same classical instance that `Analysis.ReducedGroupCStarTrace` and
its neighbours install, so the instance argument buried inside `lp.single`
matches theirs syntactically and the point-mass rewrites fire. -/
local instance compressionDecidableEq : DecidableEq G := Classical.decEq G

/-! ## Point masses -/

/-- The point mass at `g`: the vector of `ℓ²(G)` that is `1` at `g` and `0`
elsewhere.  `ReducedGroupCStarTrace.deltaOne G` is this vector at `g = 1`. -/
def pointMass (G : Type u) [Group G] (g : G) : GroupHilbert G :=
  lp.single 2 g (1 : ℂ)

theorem pointMass_def (g : G) :
    pointMass G g = lp.single 2 g (1 : ℂ) := rfl

/-- **The point masses are orthonormal.**

The same statement is proved in `Analysis.LanceFolnerMaps` for the Følner
inclusion.  It is repeated here at `pointMass` for two reasons, both
mechanical: the rewrites below must fire on a term whose head is `pointMass`
rather than `lp.single`, and this file's imports then do not have to run
through the Choi/block-operator lane, which it uses for nothing. -/
theorem pointMass_inner (s t : G) :
    ⟪pointMass G s, pointMass G t⟫_ℂ = if s = t then 1 else 0 := by
  rw [pointMass_def, pointMass_def, lp.inner_single_left]
  by_cases h : s = t
  · subst h
    rw [lp.single_apply_self, if_pos rfl]
    simp
  · rw [lp.single_apply_ne _ _ _ h, if_neg h]
    simp

/-- **Left translation permutes the point masses.** -/
theorem leftRegular_pointMass (g t : G) :
    leftRegularOperator G g (pointMass G t) = pointMass G (g * t) := by
  rw [pointMass_def, pointMass_def]
  apply lp.ext
  funext x
  rw [leftRegularOperator_apply]
  by_cases h : x = g * t
  · subst h
    rw [inv_mul_cancel_left, lp.single_apply_self, lp.single_apply_self]
  · have h' : g⁻¹ * x ≠ t := fun hc ↦ h (inv_mul_eq_iff_eq_mul.mp hc)
    rw [lp.single_apply_ne _ _ _ h', lp.single_apply_ne _ _ _ h]

/-! ## The canonical trace at an arbitrary point mass -/

/-- The canonical trace of `C⋆_r(G)`, as a plain function.  Reducible, so that
it unifies with the explicit lambda used in the statements of
`Analysis.TikuisisWhiteWinter`. -/
abbrev canonicalReducedTrace (G : Type u) [Group G] : ReducedGroupCStar G → ℂ :=
  fun T ↦ ReducedGroupCStarTrace.canonicalFaithfulTracialState G T

/-- **The canonical trace is the diagonal coefficient at *every* point mass,
not only at the identity.**

This is why the trace clause of a compression model is an equality rather than
a limit, and it is where the *right* regular representation earns its keep:
`δ_x = ρ(x) δ₁`, every element of the reduced algebra commutes with `ρ(x)`
(`reduced_commutes_right`), and `ρ(x)` is unitary, so

```text
    ⟪δ_x, a δ_x⟫ = ⟪ρ(x) δ₁, ρ(x) a δ₁⟫ = ⟪δ₁, a δ₁⟫ = τ(a).
```

No amenability, no Følner set, and no hypothesis on `x`. -/
theorem inner_pointMass_apply (a : ReducedGroupCStar G) (x : G) :
    ⟪pointMass G x,
        (a : GroupHilbert G →L[ℂ] GroupHilbert G) (pointMass G x)⟫_ℂ
      = canonicalReducedTrace G a := by
  have hδ : pointMass G x = rightRegularOperator G x (deltaOne G) :=
    (rightRegular_deltaOne G x).symm
  have hcomm : (a : GroupHilbert G →L[ℂ] GroupHilbert G)
      (rightRegularOperator G x (deltaOne G))
      = rightRegularOperator G x
        ((a : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) :=
    DFunLike.congr_fun (reduced_commutes_right G a x) (deltaOne G)
  rw [hδ, hcomm]
  have hiso : ⟪rightRegularOperator G x (deltaOne G),
        rightRegularOperator G x
          ((a : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G))⟫_ℂ
      = ⟪deltaOne G,
        (a : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)⟫_ℂ :=
    (rightRegular G x).inner_map_map _ _
  rw [hiso]
  show _ = ((a : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) 1
  rw [deltaOne, lp.inner_single_left]
  simp

/-! ## The compression -/

/-- **The compression of `C⋆_r(G)` to `k` point masses**, as a `ℂ`-linear map
into `k × k` matrices:

```text
    φ_e(a)_{pq} = ⟪δ_{e p}, a δ_{e q}⟫ .
```

Only linearity is built in.  Unitality needs `e` injective
(`compressionMap_one`); complete positivity and the trace identity hold for
every `e` and are proved below. -/
def compressionMap {k : ℕ} (e : Fin k → G) :
    ReducedGroupCStar G →ₗ[ℂ]
      Matrix (naturalFiniteModel k) (naturalFiniteModel k) ℂ where
  toFun a p q :=
    ⟪pointMass G (e p),
      (a : GroupHilbert G →L[ℂ] GroupHilbert G) (pointMass G (e q))⟫_ℂ
  map_add' a b := by
    funext p q
    show ⟪pointMass G (e p),
        ((a : GroupHilbert G →L[ℂ] GroupHilbert G)
          + (b : GroupHilbert G →L[ℂ] GroupHilbert G))
          (pointMass G (e q))⟫_ℂ
      = ⟪pointMass G (e p),
          (a : GroupHilbert G →L[ℂ] GroupHilbert G)
            (pointMass G (e q))⟫_ℂ
        + ⟪pointMass G (e p),
          (b : GroupHilbert G →L[ℂ] GroupHilbert G)
            (pointMass G (e q))⟫_ℂ
    rw [_root_.add_apply, inner_add_right]
  map_smul' c a := by
    funext p q
    show ⟪pointMass G (e p),
        (c • (a : GroupHilbert G →L[ℂ] GroupHilbert G))
          (pointMass G (e q))⟫_ℂ
      = c * ⟪pointMass G (e p),
          (a : GroupHilbert G →L[ℂ] GroupHilbert G)
            (pointMass G (e q))⟫_ℂ
    rw [_root_.smul_apply, inner_smul_right]

@[simp] theorem compressionMap_apply {k : ℕ} (e : Fin k → G)
    (a : ReducedGroupCStar G) (p q : Fin k) :
    compressionMap e a p q
      = ⟪pointMass G (e p),
        (a : GroupHilbert G →L[ℂ] GroupHilbert G) (pointMass G (e q))⟫_ℂ :=
  rfl

/-- **The compression is unital.**  The only place injectivity of `e` is used:
without it the compression of the identity carries an off-diagonal `1`. -/
theorem compressionMap_one {k : ℕ} {e : Fin k → G} (he : Function.Injective e) :
    compressionMap e 1 = 1 := by
  funext p q
  rw [compressionMap_apply]
  show ⟪pointMass G (e p),
      (1 : GroupHilbert G →L[ℂ] GroupHilbert G) (pointMass G (e q))⟫_ℂ = _
  rw [one_apply_eq_self, pointMass_inner]
  by_cases h : p = q
  · subst h
    rw [if_pos rfl, Matrix.one_apply_eq]
  · rw [if_neg (fun hc ↦ h (he hc)), Matrix.one_apply_ne h]

/-! ## The quadratic form of a compression -/

/-- **The bilinear form of a compression is the form of the operator**, read at
the two vectors the coefficient tuples name.  Everything about complete
positivity follows from this one line. -/
theorem compressionMap_form {k : ℕ} (e : Fin k → G) (a : ReducedGroupCStar G)
    (x y : Fin k → ℂ) :
    (∑ p : Fin k, ∑ q : Fin k,
        (starRingEnd ℂ) (x p) * compressionMap e a p q * y q)
      = ⟪∑ p : Fin k, x p • pointMass G (e p),
          (a : GroupHilbert G →L[ℂ] GroupHilbert G)
            (∑ q : Fin k, y q • pointMass G (e q))⟫_ℂ := by
  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [map_smul, inner_smul_right, compressionMap_apply]
  ring

/-- **A compression is completely positive.**  For a tuple `a : Fin m → A` and
coefficient vectors `w`, the defining sum is

```text
    ∑_{i,j} ⟪aᵢ vᵢ, aⱼ vⱼ⟫ = ‖∑ᵢ aᵢ vᵢ‖²,     vᵢ = ∑_q w_{iq} δ_{e q},
```

which is real and nonnegative for the same reason `⟪u, u⟫` is: it *is*
`⟪u, u⟫`.  No hypothesis on `e`, and no appeal to any structure theory of
completely positive maps --- the factorization through the ambient Hilbert
space is visible. -/
theorem isCompletelyPositiveOnMatrices_compressionMap {k : ℕ} (e : Fin k → G) :
    IsCompletelyPositiveOnMatrices (naturalFiniteModel k)
      ⇑(compressionMap e) := by
  intro m a w
  obtain ⟨v, hv⟩ : ∃ v : Fin m → GroupHilbert G,
      ∀ i : Fin m, v i = ∑ q : Fin k, w i q • pointMass G (e q) :=
    ⟨fun i ↦ ∑ q : Fin k, w i q • pointMass G (e q), fun _ ↦ rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : GroupHilbert G,
      u = ∑ i : Fin m, (a i : GroupHilbert G →L[ℂ] GroupHilbert G) (v i) :=
    ⟨_, rfl⟩
  have hterm : ∀ i j : Fin m,
      (∑ p : Fin k, ∑ q : Fin k,
          (starRingEnd ℂ) (w i p)
            * compressionMap e (star (a i) * a j) p q * w j q)
        = ⟪(a i : GroupHilbert G →L[ℂ] GroupHilbert G) (v i),
            (a j : GroupHilbert G →L[ℂ] GroupHilbert G) (v j)⟫_ℂ := by
    intro i j
    rw [compressionMap_form, ← hv i, ← hv j]
    have hco : ((star (a i) * a j : ReducedGroupCStar G) :
          GroupHilbert G →L[ℂ] GroupHilbert G) (v j)
        = ContinuousLinearMap.adjoint
            (a i : GroupHilbert G →L[ℂ] GroupHilbert G)
            ((a j : GroupHilbert G →L[ℂ] GroupHilbert G) (v j)) := by
      show (star (a i : GroupHilbert G →L[ℂ] GroupHilbert G)
        * (a j : GroupHilbert G →L[ℂ] GroupHilbert G)) (v j) = _
      rw [ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp]
    rw [hco, ContinuousLinearMap.adjoint_inner_right]
  have hgoal : (∑ i : Fin m, ∑ j : Fin m, ∑ p : Fin k, ∑ q : Fin k,
      (starRingEnd ℂ) (w i p)
        * compressionMap e (star (a i) * a j) p q * w j q) = ⟪u, u⟫_ℂ := by
    rw [hu, sum_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact hterm i j
  have hself : ⟪u, u⟫_ℂ = ((‖u‖ : ℝ) : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K u
  constructor
  · show (∑ i : Fin m, ∑ j : Fin m, ∑ p : Fin k, ∑ q : Fin k,
        (starRingEnd ℂ) (w i p)
          * compressionMap e (star (a i) * a j) p q * w j q).im = 0
    rw [hgoal, hself, ← Complex.ofReal_pow, Complex.ofReal_im]
  · show 0 ≤ (∑ i : Fin m, ∑ j : Fin m, ∑ p : Fin k, ∑ q : Fin k,
        (starRingEnd ℂ) (w i p)
          * compressionMap e (star (a i) * a j) p q * w j q).re
    rw [hgoal, hself, ← Complex.ofReal_pow, Complex.ofReal_re]
    positivity

/-- **A compression is a contraction**, by the general fact that a unital
completely positive map into a matrix algebra is one
(`Quasidiagonal.ucp_norm_le`, proved off this repository's Stinespring
dilation). -/
theorem norm_compressionMap_le {k : ℕ} {e : Fin k → G}
    (he : Function.Injective e) (a : ReducedGroupCStar G) :
    ‖compressionMap e a‖ ≤ ‖a‖ :=
  ucp_norm_le (compressionMap e) (compressionMap_one he)
    (isCompletelyPositiveOnMatrices_compressionMap e) a

/-! ## The trace clause, as an identity -/

/-- **The normalized trace of a compression is the canonical trace, exactly.**

Every diagonal entry is `τ(a)` by `inner_pointMass_apply`, so the normalized
trace is the average of `k` copies of `τ(a)`.  Positivity of `k` is the only
hypothesis and it is unavoidable: at `k = 0` the normalized trace of the empty
matrix is `0`, while `τ(1) = 1`. -/
theorem normTrace_compressionMap {k : ℕ} (hk : 0 < k) (e : Fin k → G)
    (a : ReducedGroupCStar G) :
    normTrace (naturalFiniteModel k) (compressionMap e a)
      = canonicalReducedTrace G a := by
  have hdiag : ∀ p : Fin k, compressionMap e a p p = canonicalReducedTrace G a :=
    fun p ↦ by rw [compressionMap_apply]; exact inner_pointMass_apply a (e p)
  have htrace : Matrix.trace (compressionMap e a)
      = (k : ℂ) * canonicalReducedTrace G a := by
    show (∑ p : Fin k, compressionMap e a p p) = _
    rw [Finset.sum_congr rfl fun p _ ↦ hdiag p, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hkne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  show Matrix.trace (compressionMap e a)
      / (Fintype.card (naturalFiniteModel k) : ℂ) = _
  rw [htrace, card_naturalFiniteModel, mul_comm, mul_div_assoc, div_self hkne,
    mul_one]

/-! ## Compressions of a translation -/

/-- **The incidence coefficient of the enumeration**: `1` when `g` carries the
`q`-th coordinate to the `p`-th, and `0` otherwise.

It is given a name rather than written as an `if` at each use, for a mechanical
reason worth recording.  A decidable equality on `G` is available here only
through a `local instance`, and a file that installs its own would produce a
syntactically different `ite` term, against which the rewrites below would not
fire.  Every occurrence of the incidence coefficient in this development is
this constant, so every occurrence matches. -/
def incidence {k : ℕ} (e : Fin k → G) (g : G) (p q : Fin k) : ℂ :=
  if e p = g * e q then 1 else 0

theorem incidence_eq_one {k : ℕ} {e : Fin k → G} {g : G} {p q : Fin k}
    (h : e p = g * e q) : incidence e g p q = 1 :=
  if_pos h

theorem incidence_eq_zero {k : ℕ} {e : Fin k → G} {g : G} {p q : Fin k}
    (h : ¬ (e p = g * e q)) : incidence e g p q = 0 :=
  if_neg h

/-- The coefficient of a translated point mass against a point mass is the
incidence coefficient.  Stated for an arbitrary pair of window indices, which
is the form both the defect computation and the multiplicativity computation
consume. -/
theorem inner_pointMass_leftRegular_pointMass {k : ℕ} (e : Fin k → G) (g : G)
    (p q : Fin k) :
    ⟪pointMass G (e p), leftRegularOperator G g (pointMass G (e q))⟫_ℂ
      = incidence e g p q := by
  rw [leftRegular_pointMass]
  exact pointMass_inner (e p) (g * e q)

/-- The compression of a left translation is the incidence matrix of the
enumeration: a partial permutation matrix, with a `1` exactly at the pairs
`(p, q)` for which `e p = g · e q`. -/
theorem compressionMap_leftRegular_apply {k : ℕ} (e : Fin k → G) (g : G)
    (p q : Fin k) :
    compressionMap e (reducedLeftRegular G g) p q = incidence e g p q := by
  rw [compressionMap_apply]
  show ⟪pointMass G (e p),
      leftRegularOperator G g (pointMass G (e q))⟫_ℂ = _
  rw [inner_pointMass_leftRegular_pointMass]

/-! ## The family, and the four clauses it satisfies -/

/-- **A compression family**: a sequence of injective finite tuples of group
elements, hence a sequence of compressions of `C⋆_r(G)` to matrix algebras.

This is the family of candidates the group itself supplies: compress to
finitely many coordinates of `ℓ²(G)`.

It is **not** claimed here that every quasidiagonal model of the canonical
trace has this form --- the maps Tikuisis--White--Winter produce do not, and no
theorem below says otherwise.  What is proved is what this family can do
(`Analysis.CompressionTraceLocallyFinite`) and what it cannot
(`Analysis.CompressionTraceRigidity`). -/
structure CompressionFamily (G : Type u) [Group G] where
  /-- The number of coordinates compressed to, at stage `n`. -/
  size : ℕ → ℕ
  /-- The coordinates: an injective enumeration of a finite subset of `G`. -/
  enum : ∀ n : ℕ, Fin (size n) → G
  /-- Distinct indices name distinct group elements. -/
  injective : ∀ n : ℕ, Function.Injective (enum n)

namespace CompressionFamily

variable (F : CompressionFamily G)

/-- The compression at stage `n`. -/
def map (n : ℕ) :
    ReducedGroupCStar G →ₗ[ℂ]
      Matrix (naturalFiniteModel (F.size n))
        (naturalFiniteModel (F.size n)) ℂ :=
  compressionMap (F.enum n)

@[simp] theorem map_apply (n : ℕ) (a : ReducedGroupCStar G)
    (p q : Fin (F.size n)) :
    F.map n a p q
      = ⟪pointMass G (F.enum n p),
        (a : GroupHilbert G →L[ℂ] GroupHilbert G)
          (pointMass G (F.enum n q))⟫_ℂ := rfl

/-- **The one clause a compression family is not born with**: asymptotic
multiplicativity in operator norm.  It is what makes the family a
quasidiagonal model, and the only one of the five clauses that is not
automatic. -/
def IsAsymptoticallyMultiplicative : Prop :=
  ∀ a b : ReducedGroupCStar G,
    Tendsto (fun n ↦ ‖F.map n (a * b) - F.map n a * F.map n b‖) atTop (nhds 0)

/-- **An asymptotically multiplicative compression family is a quasidiagonal
model of the canonical trace.**

Unitality, complete positivity and the trace clause are supplied by this file
for every family; the multiplicativity hypothesis is the whole of the input.
So *for compression models* the conclusion of Tikuisis--White--Winter reduces
to a single statement about operator-norm defects --- and
`Analysis.CompressionTraceRigidity` computes those defects exactly. -/
def quasidiagonalTraceModel (hpos : ∀ n : ℕ, 0 < F.size n)
    (hmul : F.IsAsymptoticallyMultiplicative) :
    QuasidiagonalTraceModel (canonicalReducedTrace G) where
  space n := naturalFiniteModel (F.size n)
  map n := F.map n
  map_one n := compressionMap_one (F.injective n)
  completelyPositive n :=
    isCompletelyPositiveOnMatrices_compressionMap (F.enum n)
  tendsto_mul := hmul
  tendsto_trace a := ShulmanTrace.tendsto_zero_of_eq_zero fun n ↦ by
    show ‖canonicalReducedTrace G a
        - normTrace (naturalFiniteModel (F.size n))
          (compressionMap (F.enum n) a)‖ = 0
    rw [normTrace_compressionMap (hpos n) (F.enum n) a, sub_self, norm_zero]

/-- The proposition-level form: such a family witnesses quasidiagonality of the
canonical trace. -/
theorem isQuasidiagonalTrace (hpos : ∀ n : ℕ, 0 < F.size n)
    (hmul : F.IsAsymptoticallyMultiplicative) :
    IsQuasidiagonalTrace (canonicalReducedTrace G) :=
  ⟨F.quasidiagonalTraceModel hpos hmul⟩

end CompressionFamily

end

end Quasidiagonal
end GroupApproximation
