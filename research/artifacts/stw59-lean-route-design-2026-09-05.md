# Lean route design for STW Problem LIX (target 3)

Architect's design for formalizing
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`.
Written 2026-09-05. Mathlib pin `81a5d257` (toolchain v4.32.0); every Mathlib
name below was checked at that revision with
`git -C /Users/user/mathlib4 grep -n <pat> 81a5d257 -- Mathlib`.

**Headline.** The parity obstruction (manuscript Lemmas 2–3) cannot be made
unconditional in this campaign. But two of the three deep topological inputs
the manuscript uses are *removable*, so the whole development reduces to
**one** named `Prop`, and that `Prop` is a purely C\*-algebraic statement about
two explicit projections — no bundles, no Chern classes, no K-theory in its
statement. Everything else is elementary and can be built now.

---

## (A) The concrete model layer

### A.0 What Mathlib actually gives at the pin

Confirmed present:

| Fact | Name / location |
|---|---|
| C\*-algebra structure on matrices over a C\*-algebra | `CStarMatrix` (`Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:44`), `instCStarRing` (:763), `instCStarAlgebra` (:817) |
| C\*-algebra structure on `C(α, A)`, **requires `[CompactSpace α]`** | `Mathlib/Analysis/CStarAlgebra/ContinuousMap.lean:45` |
| Star projections | `IsStarProjection` (`Mathlib/Algebra/Star/StarProjection.lean:27`), `Mathlib/Analysis/CStarAlgebra/Projection.lean`, `IsStarProjection.norm_le` (`Basic.lean:264`) |
| Unitary submonoid | `unitary` (`Mathlib/Algebra/Star/Unitary.lean:35`) |
| Path component of `1` in a unitary group | `Unitary.mem_pathComponentOne_iff` (`Mathlib/Analysis/CStarAlgebra/Unitary/Connected.lean:336`), `Unitary.instLocallyPathConnectedSpace` (:330), `Unitary.path` (:302), `Unitary.joined` (:311), `selfAdjoint.expUnitaryPathToOne` (:287), `Unitary.norm_sub_one_lt_two_iff` (:90) |
| Continuous functional calculus (for polar decomposition, logs, `(b*b)^{-1/2}`) | `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/*` |
| Spheres are compact as subtypes | `Metric.sphere.compactSpace` (`Mathlib/Topology/MetricSpace/ProperSpace.lean:55`), instance |
| Gluing continuous maps along a closed cover | `ContinuousMap.liftCover` / `liftCover'` (`Mathlib/Topology/ContinuousMap/Basic.lean:365`, `:392`) |
| C\*-ring structure on a `StarSubalgebra` (same unit only) | `to_cstarRing` (`Mathlib/Analysis/CStarAlgebra/Basic.lean:310`) |

Confirmed **absent** at the pin (all checked by grep over `Mathlib`):

* No Chern classes, no Euler class, no Thom class, no characteristic classes of
  any kind. `Mathlib/Geometry/Manifold/VectorBundle/*` is the fibre-bundle
  framework only.
* No topological K-theory, no K-theory of C\*-algebras, no Bott periodicity.
  The only `Grothendieck` hits are `CategoryTheory` constructions.
* No Murray–von Neumann equivalence (zero hits for `Murray`).
* No corner algebra `pAp`. `to_cstarRing` covers only subalgebras with the
  *same* unit.
* No "close projections are unitarily equivalent" and no homotopy invariance
  for projections.
* No Steenrod squares and no cup-\(i\) products anywhere (see (B)).
* `Matrix.instCStarRing` (`Mathlib/Analysis/CStarAlgebra/Matrix.lean:287`) is a
  **scoped `def`**, not a global instance. Use `CStarMatrix`, never `Matrix`,
  wherever a C\*-norm is needed.

### A.1 The model — confirmed, with one change

```
def CPd (d : ℕ) : Type :=
  {q : Matrix (Fin (d+1)) (Fin (d+1)) ℂ // qᴴ = q ∧ q * q = q ∧ q.trace = 1}
```
with the subtype topology from the finite-dimensional space of matrices.
Compact (closed and bounded: `‖q‖ ≤ 1` from `IsStarProjection.norm_le`) and
Hausdorff. The tautological line is the **identity** map `CPd d → Matrix _ _ ℂ`,
so there is no quotient topology anywhere. Confirmed as proposed.

```
def Sph (n : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1
```
`CompactSpace` comes free from the `Metric.sphere.compactSpace` instance.
Confirmed as proposed.

```
def BaseSpace (l : ℕ) (d : Fin l → ℕ) : Type := Sph 4 × (∀ j, CPd (d j))
```
`CompactSpace` from `Prod.compactSpace` and `Pi.compactSpace`.

Section algebra: **the corner is the right model**, but the proposal
`p • M • p` must be built, not found:

```
def Corner (A : Type*) [CStarAlgebra A] (p : A) : Type := {x : A // p * x = x ∧ x * p = x}
```
This is a closed non-unital star subalgebra with unit `p`. Mathlib has nothing
for this; see module `Analysis/CornerCStarAlgebra.lean` in (C). Murray–von
Neumann equivalence of projections is the bundle-isomorphism surrogate, also
new:

```
def MvNEquiv {A} [CStarAlgebra A] (p q : A) : Prop := ∃ w : A, star w * w = p ∧ w * star w = q
```

`F` over `S⁵ ⊂ ℂ³` is `x ↦ 1 - x xᴴ`, a continuous projection-valued map — as
proposed, with `Sph 5` realized inside `EuclideanSpace ℝ (Fin 6)` and the
identification `ℝ⁶ ≅ ℂ³` given explicitly (real/imaginary interleaving).

**Change to the proposal.** The hemisphere trivializations of `F` must *not* be
attempted by explicit rotation formulas; see (B.5).

---

## (B) The critical decision: the parity obstruction

### B.1 What the obstruction actually is

The manuscript's Lemma 2 with `Y = pt` says `F ≇ 1²` over `S⁵`, which is
exactly `π₄(U(2)) ≠ 0`, i.e. `π₄(SU(2)) = π₄(S³) = ℤ/2`, generated by `Ση`.
So **any** formalization of LIX along this line strictly contains a proof that
`π₄(S³) ≠ 0` — the first genuinely hard homotopy group. This is not an artifact
of the manuscript's route; the "K₁-injectivity gap" for `C(X) ⊗ Mₙ` is governed
precisely by the unstable groups `π_{2n}(U(n)) ≅ ℤ/n!`, whose smallest
nontrivial member is `π₄(U(2)) = ℤ/2`. There is no cheaper source of the
phenomenon.

Detecting `Ση ≠ 0` means detecting a class that **cup products cannot see**:
the mapping cone of `Ση` is `ΣCP²`, and all cup products vanish on a
suspension. The invariant that works is `Sq² : H³(ΣCP²; 𝔽₂) → H⁵(ΣCP²; 𝔽₂)`,
nonzero because it suspends `Sq² = (·)²` on `H²(CP²)`. Keep that sentence in
mind: it decides routes 1–3 below.

### B.2 Route 1 — reuse `SphereOddDegree`. **Verdict: no.**

I read the vendored tree (92 top-level entries plus
`AlgebraicTopology/`, `Final/`). What is there: singular chains and cochains on
`TopCat.{0}`, the Alexander–Whitney cochain cup product (`cochainCup`,
`cochainPow`, `cochainCup_naturality` in
`AlgebraicTopology/CupProduct.lean`), barycentric subdivision with its chain
homotopy, the RP\(^n\) cellular filtration, cellular cochains, cellular
diagonal, the cellular↔singular comparison, the mod-2 cohomology **ring** of
RP\(^n\), the double cover, the transfer, Gysin connecting maps, degree theory,
`no_odd_map_sphere_succ`, `borsuk_ulam`.

What is not there: **anything Steenrod**. Grepping the entire repository for
`steenrod|cup_?1|cupOne|cup_?i` returns exactly one hit, and it is a comment
naming a scaffolding step `PR-cup1` in `CupProductScaffolding.lean` — a name,
not a construction.

To get `Sq²` you need Steenrod's cup-\(i\) products: an equivariant chain
approximation to the diagonal over the standard free `ℤ/2`-resolution, built by
acyclic carriers, with naturality, the Cartan formula (or at least
`Sq^{|x|}x = x²` and `Sq^i x = 0` for `i > |x|`), and compatibility with the
suspension isomorphism. That is a multi-thousand-line development *on top of* a
base that two lanes are still bringing green on v4.32. And it is not a "modest
extension" of what is vendored: the vendored development's entire output is
statements about cup products and mod-2 degrees, and our target class is
precisely the one cup products annihilate.

### B.3 Route 2 — finite/combinatorial certificate. **Verdict: no (not a shortcut).**

The arithmetic really is small. `Sq²` on a degree-3 cocycle is the cup-1 square
`y ∪₁ y`, and Steenrod's `∪ᵢ` has a closed formula on simplicial cochains. A
9-vertex triangulation of `CP²` is classical, so `ΣCP²` has an explicit
finite model, and verifying `Sq² ≠ 0` on it is finite arithmetic over `𝔽₂` —
comfortably inside `decide` range if it were stated combinatorially (a few
hundred simplices; the cup-1 formula is a sum over front/back face splittings,
so the whole check is a few thousand `𝔽₂` multiplications).

The killer is the **bridge**, and it is fatal. Nothing in that finite
computation touches the specific continuous `u : S⁴ → U(2)` or the concrete
projection `x ↦ 1 - xxᴴ` on `S⁵ ⊂ ℂ³`. Connecting them requires: a simplicial
model of `S⁴` and of the mapping cone, simplicial approximation of `u`,
homotopy invariance of the resulting cohomology, and an identification of the
combinatorial cone with the cone of `u`. Every one of those is the expensive
machinery we were trying to avoid, and the cup-\(i\) products are still needed
on top. The arithmetic is cheap; the bridge is not.

### B.4 Route 3 — quaternionic / explicit elementary invariant. **Verdict: no.**

`SU(2) = S³` = unit quaternions and the generator of `π₄(S³)` is `Ση`; both
facts are easy. What is not available is an elementary invariant that detects
`Ση`. The Hopf invariant is defined on `π_{2n-1}(S^n)` and is identically zero
in the degrees relevant to `π₄(S³)`; the linking-number and
determinant-line/holonomy invariants one might hope for are all restrictions of
either the Hopf invariant or the Chern character, and both vanish here. The
invariant that does the job is exactly the (functional) `Sq²` of route 1. I
could not find, and do not believe there exists, an elementary integral
certificate for `Ση ≠ 0`.

### B.5 Route 4 — build Chern classes narrowly. **Verdict: no.**

To transcribe the printed proof one needs, over these specific spaces:
complex vector bundles as objects with isomorphism classes; total and top Chern
classes with the Whitney sum formula; the Euler class of the underlying
oriented real bundle as a signed transverse-zero count (orientation,
transversality, local degree, Thom class); plus Lemma 3's separate inputs
`K⁰(∏CP^{d_j})`, the Künneth isomorphism in the torsion-free case, and the
integral normalization of the Chern character on a sphere Bott generator.
Mathlib at the pin has **none** of these. This is tens of thousands of lines of
hard mathematics — a multi-year library project, not a campaign task.

### B.6 The two removable inputs (the actual design contribution)

The manuscript uses three deep topological facts. Two of them are not needed.

**Removal 1 — `K₁(A) = 0` is off the critical path.**
STW LIX asks only whether every unital simple C\*-algebra is K₁-injective. To
refute, one needs `v ∈ U(A)` with `v ∉ U₀(A)` and `[v] = 0` in `K₁(A)`. The
manuscript itself supplies `[v] = 0` *directly*, in the last paragraph of §6:
`diag(u, 1₂) : S⁴ → U(4)` is null-homotopic, and that contraction maps to a
contraction of `diag(v, 1)` in `M₂(A)`. The statement `K₁(A) = 0` needs
`K¹(X_i) = 0`, i.e. even-cell topological K-theory of products of `CP^n` plus
Bott periodicity — a *second* deep topological input, and it buys nothing.
**Do not build it. Keep it out of the endpoint.**

**Removal 2 — stable triviality is free, if `u` is defined the right way.**
The manuscript gets "`u ⊕ 1` is null-homotopic in `U(3)`" from Bott's
`π₄(U(3)) = 0`. That is avoidable, because the trivial bundle `1³` has an
*explicit* global trivialization: `ℂ³ = ℂx ⊕ x^⊥` for every `x ∈ S⁵`. Concretely:

* Hemispheres `D_± = {x ∈ S⁵ : ±Re(x₃) ≥ 0}`, each homeomorphic to `D⁵`, with
  `D₊ ∩ D₋ = {Re(x₃) = 0} ≅ S⁴`.
* Trivialize `F(x) = 1 - xxᴴ` over each `D_±`, obtaining continuous
  `V_± : D_± → ℂ^{3×2}` with `V_±ᴴ V_± = I₂` and `V_± V_±ᴴ = F`.
* Set `W_±(x) := [V_±(x) | x] ∈ U(3)` — unitary because `x` is a unit vector
  orthogonal to the range of `V_±(x)`.
* Define `u` on the equator by `W₊ᴴ W₋`. Both `W_±` send `e₃ ↦ x`, so
  `W₊(x)ᴴ W₋(x)` fixes `e₃`, hence preserves `{e₃}^⊥ = ℂ²`, hence **is** of the
  form `diag(u(x), 1)` with `u(x) ∈ U(2)`. This is the *definition* of `u`.
* Then `diag(u,1) = W₊|_{S⁴}ᴴ · W₋|_{S⁴}`, and each factor extends continuously
  over its own 5-disk, so each is null-homotopic by radial contraction, hence so
  is the product.

No Bott, no `π₄(U(3))`. Also drop `u² ≃ 1` and "order exactly two": those are
`π₄(U(2)) = ℤ/2` again, and the LIX answer does not need them.

**Trap (this cost me the first version of the design, and it will cost a lane a
week).** Do not attempt an explicit formula for a unitary `A(x) ∈ U(3)` with
`A(x)e₃ = x` continuous on a closed hemisphere. Complex Householder reflections
send `e₃` to a *phase multiple* of `x`, not to `x`. The two-dimensional geodesic
formula
```
U(x) = I + (c-1) e₃e₃ᴴ + (c̄-1) f fᴴ + s f e₃ᴴ - s e₃ fᴴ,
   c = x₃, s = ‖x - c e₃‖, f = (x - c e₃)/s
```
is continuous only on `{s > 0} ∪ {e₃}`, whose complement is the circle
`{λe₃ : |λ| = 1}` minus the single point `λ = 1`. That set is not closed, so the
domain of continuity is not open and contains no closed hemisphere. The
obstruction is real, not a formula-hunting failure.

Instead get `V_±` from three elementary C\*-lemmas (none in Mathlib):

* **(L1)** `‖p - q‖ < 1` for projections `p, q` ⟹ `MvNEquiv p q`
  (`z = qp + (1-q)(1-p)` is invertible; polar-decompose with the CFC).
* **(L2)** a continuous path of projections gives `MvNEquiv` of the endpoints
  (uniform continuity on `[0,1]`, finitely many `(L1)` steps, `MvNEquiv` is
  transitive).
* **(L3)** over a contractible compact space every projection is `MvNEquiv` to a
  constant one (compose the projection with the contracting homotopy to produce
  the path for `(L2)`).

### B.7 Verdict

**There is no unconditional Lean route to the parity obstruction at feasible
cost.** After Removals 1 and 2 the campaign has exactly **one** residue, and it
is manuscript Lemma 2 restated in Murray–von Neumann language:

```lean
/-- **Twisted cancellation failure** (manuscript Lemma 2).
Over `S⁵ × ∏_j CP^{d_j}`, the projection `F ⊕ p_H` is *not* Murray–von Neumann
equivalent to `1² ⊕ p_H` in the matrix algebra over the continuous functions on
that space, for any finite list of dimensions `d`.

Discharged by: manuscript Lemmas 2 and 3 — form the mapping-torus bundle of a
unitary implementing the equivalence, evaluate its top Chern number two ways
(an explicit transverse section with signed zero count `±⟨c_m(H),[Y]⟩ = ±1`,
against the parity calculation `c_q(δ) = (-1)^{q-1}(q-1)! ch_q(δ)` on
`K⁰(S¹ × M)`, whose every positive Chern class is even) and derive
`±1 ∈ 2ℤ`. Requires: Chern classes of complex vector bundles with the Whitney
sum formula; the Euler class of the underlying oriented real bundle as a signed
transverse-zero count; `K⁰(∏CP^{d_j})` and `K¹ = 0`; the external-product
Künneth isomorphism in the torsion-free case; and the integral normalization of
the Chern character of a sphere Bott generator. None of these exist in Mathlib
at pin 81a5d257. -/
def TwistedCancellationFailure : Prop := ...
```

The statement mentions no bundle, no Chern class, no K-group: it is a sentence
about two explicit projections in `CStarMatrix N N C(BaseSpace, ℂ)`. Everything
between that `Prop` and "there is a unital simple C\*-algebra that is not
K₁-injective" is elementary C\*-algebra plus point-set topology, and is
formalizable now.

---

## (C) The module plan

Namespace `GroupApproximation.STW.LIX`. Directory conventions follow the repo:
the `ProblemLIX*` chain lives in
`GroupApproximation/Manuscript/NinetyNineProblems/` (next to `ProblemX.lean`);
the two reusable C\*-infrastructure modules live in
`GroupApproximation/Analysis/`. Everything below is **ELEMENTARY** (buildable
now, unconditional) unless explicitly marked. Lanes author orphan modules; the
lead wires root imports.

### C.1 `lix-spaces` — concrete spaces and corner algebras. All elementary.

**`GroupApproximation/Analysis/ProjectionMvNEquivalence.lean`** *(build this
FIRST; three lanes depend on it)*

```lean
def MvNEquiv {A : Type*} [CStarAlgebra A] (p q : A) : Prop :=
  ∃ w : A, star w * w = p ∧ w * star w = q
theorem MvNEquiv.refl / .symm / .trans
theorem MvNEquiv.add_of_orthogonal      -- p₁⊥p₂, q₁⊥q₂ ⇒ p₁+p₂ ~ q₁+q₂
theorem mvnEquiv_of_norm_sub_lt_one     -- (L1)
theorem mvnEquiv_of_path                -- (L2): ContinuousMap ℝ≥0 → projections
theorem mvnEquiv_const_of_contractible  -- (L3)
```

**`GroupApproximation/Analysis/CornerCStarAlgebra.lean`**

```lean
def Corner (A : Type*) [CStarAlgebra A] (p : A) : Type := {x : A // p * x = x ∧ x * p = x}
noncomputable instance (hp : IsStarProjection p) (hp0 : p ≠ 0) : CStarAlgebra (Corner A p)
def Corner.subtypeₙₐ : Corner A p →⋆ₙₐ[ℂ] A          -- isometric star embedding
lemma Corner.one_eq : (1 : Corner A p) = ⟨p, _, _⟩
lemma Corner.mem_unitary_iff {w : Corner A p} :
    w ∈ unitary (Corner A p) ↔ star (w:A) * w = p ∧ (w:A) * star w = p
lemma Corner.mem_U0_iff -- transported `Unitary.mem_pathComponentOne_iff`
```
Mathlib has nothing for this (`to_cstarRing` at `Basic.lean:310` covers only
the same-unit case). Roughly 300–400 lines; the only delicate points are
`NormedRing` (`‖p‖ = 1` gives `NormOneClass`) and completeness (closed subspace).

**`.../NinetyNineProblems/ProblemLIXSpaces.lean`**

```lean
def CPd (d : ℕ) : Type
instance : TopologicalSpace (CPd d)   instance : CompactSpace (CPd d)   instance : T2Space (CPd d)
def taut (d : ℕ) : C(CPd d, Matrix (Fin (d+1)) (Fin (d+1)) ℂ)   -- the identity; the tautological line
lemma taut_isStarProjection

def Sph (n : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1
def BaseSpace {l : ℕ} (d : Fin l → ℕ) : Type := Sph 4 × (∀ j, CPd (d j))
instance : CompactSpace (BaseSpace d)

def rk {l} (d : Fin l → ℕ) : ℕ := 2 + ∑ j, (d j + 1) * (mult j)   -- N; block sizes explicit
def Hproj {l} (d : Fin l → ℕ) : CStarMatrix (Fin (rk d)) (Fin (rk d)) C(BaseSpace d, ℂ)
def Eproj {l} (d : Fin l → ℕ) : ... := blockDiag 1₂ (Hproj d)
lemma Eproj_isStarProjection

def blockAlg {l} (d : Fin l → ℕ) : Type := Corner _ (Eproj d)      -- A_i
noncomputable instance : CStarAlgebra (blockAlg d)
```

Traps: `C(α, A)` is a C\*-algebra only with `[CompactSpace α]`; use
`CStarMatrix`, never `Matrix`, since `Matrix.instCStarRing` is a scoped `def`;
`CPd` compactness needs `‖q‖ ≤ 1` (`IsStarProjection.norm_le`) plus closedness
of the three defining equations.

### C.2 `lix-clutching` — the explicit unitary and the clutching map. All elementary.

**`.../NinetyNineProblems/ProblemLIXClutching.lean`**

```lean
def Fproj : C(Sph 5, CStarMatrix (Fin 3) (Fin 3) ℂ)          -- x ↦ 1 - x xᴴ
lemma Fproj_isStarProjection
def Dplus / Dminus : Set (Sph 5)                              -- ±Re x₃ ≥ 0
lemma isClosed_Dplus / _Dminus,  lemma Dplus_union_Dminus,  lemma Dplus_inter_Dminus_homeo_sph4
lemma contractible_Dplus / _Dminus

-- (L3) applied twice:
lemma exists_frame : ∃ V₊ : C(Dplus, Matrix (Fin 3) (Fin 2) ℂ), V₊ᴴV₊ = 1 ∧ V₊V₊ᴴ = Fproj  -- and V₋

noncomputable def W (ε : Bool) : C(D ε, CStarMatrix (Fin 3) (Fin 3) ℂ)   -- [V ε | x]
lemma W_unitary
noncomputable def u : C(Sph 4, CStarMatrix (Fin 2) (Fin 2) ℂ)            -- from W₊ᴴW₋, by choice
lemma u_unitary
theorem diag_u_one_eq : (diag (u x) 1 : U(3)) = (W true x)ᴴ * (W false x) 
theorem diag_u_one_mem_U0 : diag u 1 ∈ pathComponentOne (unitary C(Sph 4, CStarMatrix (Fin 3) (Fin 3) ℂ))

-- the clutching construction, in projection language
noncomputable def clutch {l} (d) (w : unitary (blockAlg d)) :
    CStarMatrix (Fin (rk d)) (Fin (rk d)) C(Sph 5 × (∀ j, CPd (d j)), ℂ)
lemma clutch_isStarProjection
lemma clutch_one : clutch d 1 = blockDiag 1₂ (Hproj' d)
lemma clutch_u   : clutch d (w d) = blockDiag (Fproj ⊗ 1) (Hproj' d)
theorem mvnEquiv_clutch_of_mem_U0 :
    w ∈ pathComponentOne (unitary (blockAlg d)) → MvNEquiv (clutch d w) (clutch d 1)
```

`clutch` glues over the closed cover `{D₊ × Y, D₋ × Y}` with
`ContinuousMap.liftCover'`. `mvnEquiv_clutch_of_mem_U0` is the Corollary-4
direction; it is real unconditional content and it is exactly what lets the
residue be Lemma 2 rather than "`w ∉ U₀`". `u` comes from `Classical.choose` on
`exists_frame`; nothing downstream needs `u` to be "the generator".

### C.3 `lix-obstruction` — the residue and its elementary consumers.

**`.../NinetyNineProblems/ProblemLIXObstruction.lean`**

```lean
def TwistedCancellationFailure : Prop :=
  ∀ {l : ℕ} (d : Fin l → ℕ), ∀ j, 0 < d j →
    ¬ MvNEquiv (blockDiag (Fproj ⊗ 1) (Hproj' d)) (blockDiag 1₂ (Hproj' d))

theorem w_notMem_U0 (h : TwistedCancellationFailure) {l} (d : Fin l → ℕ) :
    (w d) ∉ pathComponentOne (unitary (blockAlg d))
```

That is the whole module: the `Prop` with the docstring of (B.7), and the
one-line consequence via `mvnEquiv_clutch_of_mem_U0`. **This lane must not
attempt Chern classes, K-theory, or Steenrod squares.** Its real job is to make
the `Prop` statement tight enough that the docstring is a complete recipe for a
future discharge.

### C.4 `lix-limit` — the inductive system. All elementary.

**`.../NinetyNineProblems/ProblemLIXFiniteStage.lean`** *(start here — zero
dependencies on the other lanes)*

```lean
/-- Manuscript Lemma 7. -/
theorem mem_U0_of_mem_U0_of_isDirected
    {B : Type*} [CStarAlgebra B] (Bi : ℕ → StarSubalgebra ℂ B)
    (hmono : Monotone Bi) (hdense : Dense (⋃ i, (Bi i : Set B)))
    {k : ℕ} {a : B} (ha : a ∈ Bi k) (hu : a ∈ unitary B)
    (h0 : ⟨a, hu⟩ ∈ pathComponentOne (unitary B)) :
    ∃ j ≥ k, (path to 1 stays inside Bi j)
```
Proof exactly as printed: partition with steps `< 1/4`, approximate by
`bᵥ ∈ B_j` within `ε = 1/100`, `qᵥ = bᵥ(bᵥ*bᵥ)^{-1/2}` via the CFC,
`‖qᵥ - qᵥ₋₁‖ < 1/4 + 4ε < 2`, then `Unitary.path` / `Unitary.joined`
(`Unitary/Connected.lean:302, :311`) on each step. Mathlib has every ingredient.
~250 lines, self-contained; the best first target in the whole campaign.

**`.../NinetyNineProblems/ProblemLIXLimit.lean`**

```lean
def dims (i : ℕ) : Fin i → ℕ                                   -- r_j = 2^(j+1)
noncomputable def phi (i : ℕ) : blockAlg (dims i) →⋆ₐ[ℂ] blockAlg (dims (i+1))   -- (4.3)
lemma phi_injective, lemma phi_unital
noncomputable def limitAlg : Type
noncomputable instance : CStarAlgebra limitAlg
theorem limitAlg_separable / _unital / _infiniteDimensional
theorem limitAlg_isSimple                                       -- manuscript Lemma 5, positive cutdown
theorem limitAlg_stablyFinite                                   -- faithful trace from the inverse system
theorem v_homotopic_w (i) : ...                                 -- manuscript Lemma 6
```

**Recommendation on `limitAlg`:** Mathlib has no inductive limit of
C\*-algebras and building the general theory is a trap. Realize every `A_i`
concretely inside one fixed containing C\*-algebra (a faithful representation on
a single separable Hilbert space, or the `l∞`-product of the `A_i` modulo the
`c₀`-ideal restricted to coherent sequences) and define `limitAlg` as the
**closure of the union** of an increasing chain of `StarSubalgebra`s. Then
`ProblemLIXFiniteStage` applies verbatim, and simplicity/traces are statements
about a closed subalgebra rather than about a colimit cocone.

### C.5 `ktheory-k1` — K₁ and the reduction. All elementary.

**`GroupApproximation/Analysis/KOneUnitary.lean`**

```lean
def stablyNull {A} [CStarAlgebra A] (u : unitary A) : Prop :=
  ∃ n : ℕ, blockDiag u (1 : CStarMatrix (Fin n) (Fin n) A) ∈
    pathComponentOne (unitary (CStarMatrix (Fin (n+1)) (Fin (n+1)) A))
def KOne (A) : Type                                  -- colim_n unitary (Mₙ A) ⧸ pathComponentOne
noncomputable instance : CommGroup (KOne A)
def kOneClass {A} : unitary A →* KOne A
theorem kOneClass_eq_one_iff {u} : kOneClass u = 1 ↔ stablyNull u
def K1Injective (A) : Prop :=
  Function.Injective (QuotientGroup.lift _ kOneClass _ :
    unitary A ⧸ pathComponentOne (unitary A) → KOne A)
theorem not_k1Injective_of_stablyNull_of_notMem_U0 {u : unitary A}
    (h₁ : u ∉ pathComponentOne (unitary A)) (h₂ : stablyNull u) : ¬ K1Injective A
```
Mathlib has no C\*-K-theory at the pin; this is all new, and all elementary
group theory plus `Unitary/Connected`. `KOne` may be built as the quotient of
`Σ n, unitary (Mₙ A)` by "become homotopic after further stabilization"; the
directed-colimit route needs a `Monoid.DirectLimit`-style construction that is
not worth chasing.

### C.6 Assembly (lead wires the root import)

**`.../NinetyNineProblems/ProblemLIX.lean`**

```lean
theorem exists_simple_unital_not_k1Injective (h : TwistedCancellationFailure) :
    ∃ (A : Type) (_ : CStarAlgebra A), IsSimpleCStar A ∧ ¬ K1Injective A
```

**This is a REDUCTION, not an endpoint.** Standing rule 3 forbids endpoint
statements that mention a residue `Prop`. While `TwistedCancellationFailure` is
undischarged this theorem must **not** be registered as a closed endpoint for
STW LIX, must not appear in the endpoint/audit roster as such, and must not be
cited in the manuscript as answering Problem LIX in Lean.

### C.7 Dependency order (what unblocks what)

```
ProjectionMvNEquivalence ──┬─> CornerCStarAlgebra ──> ProblemLIXSpaces ──┬─> ProblemLIXClutching ──> ProblemLIXObstruction ─┐
                           │                                            └─> ProblemLIXLimit ───────────────────────────────┼─> ProblemLIX
ProblemLIXFiniteStage (independent) ─────────────────────────────────────────────────────────────────────────────────────┤
KOneUnitary (independent) ───────────────────────────────────────────────────────────────────────────────────────────────┘
```
`ProblemLIXFiniteStage` and `KOneUnitary` have no dependencies and should be
started immediately, in parallel with `ProjectionMvNEquivalence`.

---

## (D) The honest ledger

**Can be made fully unconditional in this campaign** (all of it is elementary
C\*-algebra and point-set topology; none of it needs a library Mathlib lacks):

1. `MvNEquiv` and its calculus, including (L1)–(L3).
2. Corner C\*-algebras `pAp`.
3. `CP^d` and `S^n` as concrete compact Hausdorff spaces; the tautological
   projection as the identity map.
4. The block algebras `A_i = Γ(X_i, End E_i)` as corners.
5. The hemisphere decomposition of `S⁵`, the frames `V_±`, the unitaries `W_±`,
   the witness `u`, and `diag(u,1) ∈ U₀` — **including the stable triviality
   that the manuscript takes from Bott** (Removal 2).
6. The clutching construction in projection language and
   `w ∈ U₀ ⇒ MvNEquiv (clutch w) (clutch 1)` (Corollary 4's contrapositive).
7. The twisted point evaluations `φ_i`, their well-definedness, unitality and
   injectivity.
8. Simplicity of the limit (manuscript Lemma 5, positive-cutdown argument).
9. Stable finiteness via the inverse limit of tracial state spaces and
   faithfulness from simplicity.
10. Separability, unitality, infinite-dimensionality.
11. Manuscript Lemma 6 (finite-stage homotopy `v_i ≃ w_i`).
12. Manuscript Lemma 7 (finite-stage detection of a null-homotopy).
13. `KOne`, `stablyNull`, `K1Injective`, and
    `¬K1Injective` from "not in `U₀`" + "stably null".
14. The reduction theorem of C.6.

**Must stand as a residue — exactly one named `Prop`:**

`TwistedCancellationFailure` = manuscript Lemma 2. Discharging it needs Chern
classes with the Whitney sum formula, the Euler class as a transverse-zero
count, `K⁰(∏CP^{d_j})`, the Künneth isomorphism, and Chern-character
integrality — none of which exist in Mathlib at the pin, and each of which is a
library-scale project. The campaign's honest output is *"LIX reduces to this
one sentence about two explicit projections"*, **not** *"LIX is closed"*.

**Explicitly NOT needed — do not build, and do not let a lane drift into them:**

* `K₁(A) = 0` (needs `K¹(X_i) = 0`, i.e. Bott periodicity).
* `π₄(U(3)) = 0` (replaced by Removal 2).
* `π₄(U(2)) = ℤ/2`, `u² ≃ 1`, and "the class of `v` has order exactly two".
* Steenrod squares, cup-\(i\) products, simplicial models of `CP²`.
* Any general theory of inductive limits of C\*-algebras.

**Honesty note on the optimistic column.** Items 1–14 are elementary in the
mathematical sense, but they are not small: my estimate is 4000–6000 lines of
Lean, with `ProjectionMvNEquivalence`, `CornerCStarAlgebra`,
`ProblemLIXFiniteStage` and `ProblemLIXLimit`'s simplicity proof being the four
substantial pieces. Nothing in them is research; all of it is grinding. The one
place where a lane could discover a genuine obstruction is C.4's `limitAlg`
construction, if the concrete-realization trick turns out to be awkward — that
is the item to report on first.
