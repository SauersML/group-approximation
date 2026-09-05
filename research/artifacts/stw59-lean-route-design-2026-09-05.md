# Lean route design for STW Problem LIX (target 3)

Architect's design for formalizing
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`
**fully unconditionally, with no residue**. Mathlib pin `81a5d257` (toolchain
v4.32.0); every Mathlib name below was checked at that revision with
`git -C /Users/user/mathlib4 grep -n <pat> 81a5d257 -- Mathlib`.

Revision 2 (2026-09-05, later): the mandate changed from "find the cheapest
route that avoids the missing foundations" to "build the foundations". The
honest-ledger section of revision 1 is superseded: **nothing here remains a
named `Prop` residue.** What survives from revision 1 is the concrete model
layer, the two removals in §B.6, and the elementary C\*-algebra half of the
module plan — all of which the new mandate keeps unchanged.

Twelve lanes: five LIX lanes (`lix-spaces`, `lix-clutching`,
`lix-obstruction`, `lix-limit`, `ktheory-k1`) and seven foundation lanes
(`found-bundle-calculus`, `found-cohomology-ring`, `found-cpn-cohomology`,
`found-chern-classes`, `found-ktheory-bott`, `found-euler-class`,
`found-mapping-torus-parity`).

---

## (A) The concrete model layer

### A.0 What Mathlib gives at the pin

| Fact | Name / location |
|---|---|
| C\*-algebra on matrices over a C\*-algebra | `CStarMatrix` (`Analysis/CStarAlgebra/CStarMatrix.lean:44`), `instCStarRing` (:763), `instCStarAlgebra` (:817) |
| C\*-algebra on `C(α, A)`, **requires `[CompactSpace α]`** | `Analysis/CStarAlgebra/ContinuousMap.lean:45` |
| Star projections | `IsStarProjection` (`Algebra/Star/StarProjection.lean:27`), `IsStarProjection.norm_le` (`Analysis/CStarAlgebra/Basic.lean:264`) |
| Unitary submonoid | `unitary` (`Algebra/Star/Unitary.lean:35`) |
| Path component of `1` in a unitary group | `Unitary.mem_pathComponentOne_iff` (`Analysis/CStarAlgebra/Unitary/Connected.lean:336`), `Unitary.path` (:302), `Unitary.joined` (:311), `selfAdjoint.expUnitaryPathToOne` (:287), `Unitary.norm_sub_one_lt_two_iff` (:90), `Unitary.instLocallyPathConnectedSpace` (:330) |
| Continuous functional calculus | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/*` |
| Spheres compact as subtypes | `Metric.sphere.compactSpace` (`Topology/MetricSpace/ProperSpace.lean:55`), an instance |
| Gluing along a closed cover | `ContinuousMap.liftCover` / `liftCover'` (`Topology/ContinuousMap/Basic.lean:365`, `:392`) |
| C\*-ring on a `StarSubalgebra` (same unit only) | `to_cstarRing` (`Analysis/CStarAlgebra/Basic.lean:310`) |

Absent at the pin, all verified by grep over `Mathlib`: characteristic classes
of any kind; topological or C\*-algebraic K-theory; Bott periodicity; Murray–von
Neumann equivalence (zero hits for `Murray`); corner algebras; "close
projections are unitarily equivalent"; homotopy invariance for projections;
Steenrod squares and cup-\(i\) products. Also: `Matrix.instCStarRing`
(`Analysis/CStarAlgebra/Matrix.lean:287`) is a **scoped `def`**, not a global
instance — use `CStarMatrix`, never `Matrix`, wherever a C\*-norm is needed.

### A.1 The model

```
CPd d  := {q : Matrix (Fin (d+1)) (Fin (d+1)) ℂ // qᴴ = q ∧ q*q = q ∧ q.trace = 1}
Sph n  := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1
Gr n N := {q : Matrix (Fin N) (Fin N) ℂ // qᴴ = q ∧ q*q = q ∧ q.trace = n}
```
all with the subtype topology from the finite-dimensional matrix space; all
compact Hausdorff. **A complex vector bundle over a compact Hausdorff `X` is a
continuous projection-valued map `p : C(X, CStarMatrix (Fin N) (Fin N) ℂ)`**,
and bundle isomorphism is Murray–von Neumann equivalence. There is no quotient
topology anywhere in the campaign, the tautological line over `CPd d` is the
identity map, and a rank-`n` bundle *is* its own classifying map `X → Gr n N`.

Section algebras are corners: `Corner A p := {x : A // p*x = x ∧ x*p = x}`,
a unital C\*-algebra with unit `p`.

`F` over `Sph 5 ⊂ ℂ³` is `x ↦ 1 - x xᴴ`, with `Sph 5` inside
`EuclideanSpace ℝ (Fin 6)` and an explicit `ℝ⁶ ≅ ℂ³`.

**Change of line bundle from the manuscript (§B.6, W4(ii)).** Where the
manuscript writes `L_j` for the tautological line, we use its **conjugate**
`q ↦ q̄` (that is, `O(1)` rather than `O(-1)`). It is a rank-one projection, it
depends continuously on `q`, its `c₁` is the hyperplane class so
`⟨c₁^d, [CP^d]⟩ = 1` exactly as required, and — the reason for the change — it
has an **explicit section with exactly one nondegenerate zero**: for
`w₁,…,w_d ∈ ℂ^{d+1}`,
```
q ↦ (conj (q w₁), …, conj (q w_d))
```
is a section of `(conj taut)^{⊕d}` vanishing precisely when `range q ⊥ wᵢ` for
all `i`, i.e. at the single point cut out by the line `{w₁,…,w_d}^⊥`, where
transversality is a linear-algebra check. Nothing else in the construction
distinguishes the two lines.

---

## (B) The route we build

### B.1 The shape of the proof

Unchanged from the manuscript: on `S⁵ × Y` with `Y = ∏ CP^{d_j}`,
`H = ⊕_j L_j^{⊕d_j}`, `V = 1³ ⊕ H`, `M = S⁵ × Y`, `r = m + 3`:

* **Lemma 2 (odd side).** An isomorphism `F ⊕ H ≅ 1² ⊕ H` yields a unitary
  automorphism `g` of `V` with `g e = s`; the mapping-torus bundle `W_g` over
  `S¹ × M` carries the explicit section (2.10) with exactly one nondegenerate
  zero, so `⟨c_r(W_g), [S¹×M]⟩ = ±1`.
* **Lemma 3 (even side).** Every rank-`r` bundle `W` over `S¹ × M` restricting
  to `V` on a slice has `⟨c_r(W), [S¹×M]⟩ ∈ 2ℤ`.
* Contradiction.

### B.2 W1 — no Steenrod squares, no Stiefel–Whitney classes, no Wu formula

Revision 1 identified `Sq²` as the only route *given the missing foundations*.
With Chern classes and the Chern character present, the integral route covers
`q = 3` as well, since `c_q(δ) = ±(q-1)(q-2)·(integral class)` and
`(3-1)(3-2) = 2`. So Steenrod is redundant.

The converse also fails, and it is worth recording exactly where, so that no
lane re-proposes it. With `c(δ) = 1 + z·γ` and `z² = 0`, the Wu formula for
Chern classes gives `Sq^{2k} c_i(δ) = C(i-1, k) · c_{i+k}(δ)`. From
`c₁(δ) = c₂(δ) = 0` one reaches `c₃(δ) = Sq² c₂(δ) = 0` — precisely the
`Y = point` case, i.e. `π₄(S³) ≠ 0` — but `c₄` is unreachable: `(i,k) = (3,1)`
gives `C(2,1) = 2`, `(2,2)` gives `C(1,2) = 0`, `(1,3)` gives `C(0,3) = 0`.
Concretely for `Y = CP¹`: `γ = γ₀ + γ₁h`, `c₄(δ) = ±6 z γ₁`, and `γ₁ = 1/6`
satisfies every cohomological and mod-2 constraint while making `c₄(δ)` odd.
The parity is a 2-adic fact about factorials that mod-2 methods cannot see.

### B.3 W2 — the K-theory lane shrinks to one lemma

The manuscript computes `K⁰(Y) = ⊗_j ℤ[L_j]/((L_j-1)^{d_j+1})`, needs it
generated by line monomials, and needs a K-theoretic Künneth for `Y`. All of
that is deletable, in two steps.

**(a) The shape of `ch(δ)` is pure cohomology.** `ch(δ)` lies in even degrees;
`ch(δ)|_{{1}×M} = ch(0) = 0`; by Künneth `H^*(S¹×M) = H^*(M) ⊕ t·H^*(M)` with
restriction killing the `t`-part, so `ch(δ) ∈ t·H^*(M;ℚ)`; even degree forces
the cofactor into `H^{odd}(M;ℚ)`, and `H^{odd}(S⁵×Y;ℚ) = x·H^{even}(Y;ℚ)`
because `Y` has cohomology only in even degrees. Hence
```
ch(δ) = t·x·γ = z·γ,      γ ∈ H^{even}(Y;ℚ).
```
The same argument with `ℤ` coefficients gives `c_q(δ) ∈ z·H^{even}(Y;ℤ)`, since
`c(δ)|_M = c(δ|_M) = 1` and `H^*(M;ℤ)` is torsion-free.

**(b) The integrality is the only K-theoretic input, and Newton does most of
it.** Because `z² = 0` all products of positive components of `ch(δ)` vanish, so
exponentiating `log c(δ) = Σ_q (-1)^{q-1}(q-1)!\,ch_q(δ)` gives
```
c_q(δ) = (-1)^{q-1} (q-1)! · z · γ_{q-3}.
```
Writing `(q-1)! = (q-1)(q-2)·(q-3)!` and noting `(q-1)(q-2)` is even, evenness
of `c_q(δ)` follows from `(q-3)!·γ_{q-3}` being integral. If `γ = ch(β)` for
some `β ∈ K⁰(Y)` then `k!·ch_k(β) = p_k(c(β))` is integral by **Newton's
identity** — no computation of `K⁰(Y)`, no line monomials, no K-Künneth for `Y`.

So the entire target of `found-ktheory-bott` is:

> **(KT-min)** Let `Y` be a finite complex with cells only in even dimensions
> and let `δ ∈ K⁰(S¹ × S⁵ × Y)` restrict to `0` on `{1} × S⁵ × Y`. Then there is
> `β ∈ K⁰(Y)` with `ch(δ) = z · ch(β)`, where `z = t·x`.

Bott periodicity is needed only for the normalization `ch(K̃(S^{2n})) = ℤ`, and
Künneth only for `S¹ × S⁵ × Y`. Scope the lane to that and nothing more.

### B.4 W3 — all K-theory is C\*-algebraic K-theory of `C(X)`; no Serre–Swan

Bundles are already projections, so set `K⁰(X) := K₀(C(X))` (Grothendieck group
of MvN classes of projections over `C(X)`) and `K¹(X) := K₁(C(X))`. This
unifies `found-ktheory-bott` with `ktheory-k1`, deletes Serre–Swan entirely,
and makes `found-bundle-calculus`'s homotopy invariance of bundles *literally*
lemma (L2) of `ProjectionMvNEquivalence.lean`: a homotopy of maps induces a path
of projections, and a path of projections is an MvN equivalence.

### B.5 W4 — two geometric-side simplifications

**(i) No Poincaré duality, no fundamental classes.** Every evaluation the proof
needs — `⟨c_r(W),[S¹×S⁵×Y]⟩` and `⟨c_m(H),[Y]⟩` — is against the top class of a
product of spheres and complex projective spaces, where `H^{top} ≅ ℤ` by
Künneth. Define the pairing as the coefficient with respect to the Künneth
generator. `found-cohomology-ring` must **not** build Poincaré duality.

**(ii) One zero, not a sum.** With the `O(1)` model of §A.1 the section (2.10)
has exactly one nondegenerate zero, so `found-euler-class` needs only
"one nondegenerate zero ⟹ `⟨e(W),[N]⟩ = ±1`" — never a sum over a zero set,
never Sard, never general transversality.

### B.6 The two removals from revision 1, retained

**Removal 1 — `K₁(A) = 0` is off the critical path.** LIX asks only for failure
of K₁-injectivity: `v ∉ U₀(A)` together with `[v] = 0` in `K₁(A)`, and the
manuscript supplies the latter directly (`diag(v,1) ∈ U₀(M₂A)`). `K₁(A) = 0`
would need `K¹(X_i) = 0` for every stage — a second, independent K-theory
computation that buys nothing. Keep it out of the endpoint.

**Removal 2 — stable triviality is free.** Define `u` not as "a generator of
`π₄(U(2))`" but by hemisphere comparison of frames for `F(x) = 1 - xxᴴ`:
`D_± = {x ∈ S⁵ : ±Re(x₃) ≥ 0}`, frames `V_±` from (L3), `W_±(x) = [V_±(x) | x]
∈ U(3)`, and `u := W₊ᴴW₋` on the equator — which fixes `e₃`, hence preserves
`ℂ²`, hence *is* `diag(u,1)`. Each `W_±|_{S⁴}` extends over its own 5-disk, so
each is null-homotopic by radial contraction, and so is the product. No Bott, no
`π₄(U(3))`. Correspondingly `u² ≃ 1` and "order exactly two" are dropped: they
are `π₄(U(2)) = ℤ/2` again and the LIX answer does not need them.

**Trap.** Do not attempt an explicit formula for a unitary `A(x) ∈ U(3)` with
`A(x)e₃ = x` continuous on a closed hemisphere. Complex Householder reflections
send `e₃` to a *phase multiple* of `x`; the two-dimensional geodesic formula
```
U(x) = I + (c-1)e₃e₃ᴴ + (c̄-1)ffᴴ + s f e₃ᴴ - s e₃ fᴴ,
  c = x₃, s = ‖x - c e₃‖, f = (x - c e₃)/s
```
is continuous only on `{s>0} ∪ {e₃}`, whose complement is the circle
`{λe₃ : |λ|=1}` minus the single point `λ=1` — not closed, so the domain of
continuity is not open and contains no closed hemisphere. The obstruction is
real. Use (L1)–(L3) instead.

### B.7 One structural saving for `found-mapping-torus-parity`

Lemma 3 need not quantify over all `W`. Every `W` over `S¹ × M` restricting to
`V` on a slice **is** a mapping torus `W_g`: cut `S¹` at `1`, apply homotopy
invariance over `[0,1] × M` (again just (L2)) to get `W ≅ p*V` there, and the
two ends differ by an automorphism `g` of `V`. The lane may assume `W = W_g`.

### B.8 Net effect on the seven foundation lanes

* `found-cohomology-ring` — loses Steenrod squares and Poincaré duality.
* `found-cpn-cohomology` — keeps `H^*(CP^n;ℤ)` and Künneth, loses `K^*(CP^n)`.
* `found-ktheory-bott` — collapses to (KT-min) plus what it needs.
* `found-euler-class` — loses transversality theory; one zero only.
* `found-chern-classes` — **unchanged, and now the critical path.**
* `found-bundle-calculus` — inherits homotopy invariance and trivialization
  from (L2)/(L3); its new work is `⊗`, dual, clutching and the mapping torus.
* `found-mapping-torus-parity` — may assume `W = W_g`.

---

## (C) The cross-lane graph

### C.1 Layers

| Layer | Module | Owner | Contents |
|---|---|---|---|
| L0 | `Analysis/ProjectionMvNEquivalence.lean` | `lix-spaces` | `MvNEquiv`; (L1) `‖p-q‖<1`; (L2) path of projections; (L3) contractible base; block sums |
| L0 | `Analysis/CornerCStarAlgebra.lean` | `lix-spaces` | `Corner A p` and its `CStarAlgebra` instance |
| L0 | `Topology/ConcreteSpaces.lean` | `lix-spaces` | `Sph n`, `CPd d`, `Gr n N`, `BaseSpace`, compactness, `ℝ^{2k} ≅ ℂ^k` |
| L0 | `Analysis/KOneUnitary.lean` | `ktheory-k1` | `K₁` of a C\*-algebra |
| L0 | `Analysis/KZeroProjection.lean` | `ktheory-k1` | `K₀` of a C\*-algebra |
| L1 | `Topology/BundleProj.lean` | `found-bundle-calculus` | bundle = projection; rank, `⊕`, `⊗`, dual, pullback; `Iso := MvNEquiv`; homotopy invariance; clutching over a closed cover; mapping torus |
| L2 | `Topology/SingularCohomologyRing.lean` | `found-cohomology-ring` | graded ring `H^*(−;R)`, naturality, homotopy invariance, Mayer–Vietoris, `H^*(Sⁿ)`, free-case Künneth, top-class pairing |
| L3 | `Topology/CPnCohomology.lean` | `found-cpn-cohomology` | `H^*(CPd d;ℤ) ≅ ℤ[h]/(h^{d+1})`; products; the Künneth generator |
| L4 | `Topology/ChernClasses.lean` | `found-chern-classes` | projective bundle formula, Leray–Hirsch, `c_i`, Whitney, splitting principle, naturality, `c(δ) = c(W)c(V)^{-1}`, Newton polynomials `p_k`, `ch` |
| L5a | `Topology/EulerClass.lean` | `found-euler-class` | `e = c_top`; one nondegenerate zero ⟹ `⟨e,[N]⟩ = ±1` |
| L5b | `Topology/KTheoryBott.lean` | `found-ktheory-bott` | `ch` additive/multiplicative on `K⁰`; `ch(K̃(S^{2n})) = ℤ`; (KT-min) |
| L6 | `Topology/MappingTorusParity.lean` | `found-mapping-torus-parity` | manuscript Lemma 3 |
| L7 | `Manuscript/NinetyNineProblems/ProblemLIX*.lean` | the five LIX lanes | as in §C.4 |

Edges: `L0 → L1 → {L4, L5a, L5b}`; `L2 → L3 → L4 → {L5a, L5b} → L6 →
lix-obstruction → {lix-clutching, lix-limit} → ProblemLIX`. `ktheory-k1` feeds
both L5b and the endpoint.

**Critical path:** `L2 → L3 → L4 → L5b → L6`. `found-chern-classes` is the
bottleneck and `found-cohomology-ring` gates it. `found-euler-class` and all
five LIX lanes are off the critical path and can run throughout.

**Ordering trap.** `found-cpn-cohomology` must land **before**
`found-chern-classes`, not in parallel: `c₁` of a line bundle is defined as the
pullback of the generator of `H²(CP^N)` along the classifying map, so
`H^*(CP^n)` is an *input* to Chern classes, not an output. If
`found-chern-classes` tries to define `c₁` first, the two lanes deadlock.

### C.2 Single-owner table

| Object | Defined once by | Everyone else |
|---|---|---|
| `MvNEquiv`, (L1)(L2)(L3) | `lix-spaces` | imports |
| `Corner p A p` | `lix-spaces` | imports |
| `Sph n`, `CPd d`, `Gr n N` | `lix-spaces` | imports, never redefines |
| bundle, pullback, `⊕`, `⊗`, clutch, mapping torus | `found-bundle-calculus` | imports |
| `H^*(−;R)`, cup, Künneth, top pairing | `found-cohomology-ring` | imports |
| `H^*(CP^n)`, the class `h` | `found-cpn-cohomology` | imports |
| `c_i`, splitting principle, `p_k`, `ch` | `found-chern-classes` | imports |
| Euler class, `e = c_top`, zero count | `found-euler-class` | imports |
| `K⁰(X) := K₀(C(X))`, `K¹(X) := K₁(C(X))` | `ktheory-k1` | `found-ktheory-bott` uses |
| Bott normalization, (KT-min) | `found-ktheory-bott` | imports |

### C.3 Collision risks

**C1 (highest) — the cohomology theory itself.** `found-cohomology-ring` must
**extend** `GroupApproximation/ThirdParty/HamSandwich/SphereOddDegree/AlgebraicTopology/`,
not restart. That tree already has singular chains and cochains on `TopCat.{0}`,
Alexander–Whitney, barycentric subdivision with its chain homotopy,
cellular/singular comparison, Mayer–Vietoris, and a cup product that is already
coefficient-general — `cochainCup {R : Type} [CommRing R] {Z : TopCat.{0}} (p q : ℕ)`
in `CupProduct.lean`, with `CohomologyCupProduct.lean` above it. Restarting
costs the campaign months. Two lanes are bringing that tree green on v4.32 right
now, so `found-cohomology-ring` must coordinate with them rather than fork.

**C2 — the sphere model.** Three sphere types are about to exist:
`Metric.sphere` in `EuclideanSpace` (this design), the vendored `TopCat.{0}`
model, and whatever `found-cohomology-ring` picks. A bridge file already
exists: `SphereOddDegree/SphereModelTransport.lean`. Require exactly one
transport, stated once, from `Sph n` to the model the cohomology is computed in.

**C3 — the `CP^n` model.** `found-cpn-cohomology` must use `lix-spaces`' `CPd d`
(rank-one projections, subspace topology). A quotient-topology `CP^n` is
**fatal**, not merely duplicative: the whole design rests on the tautological
line's projection being the identity map on `CPd`, which is what makes `H`, `E`
and the explicit section available. Note also §A.1: the line actually used is
`q ↦ q̄`.

**C4 — the projection model of a bundle.** Six lanes need "bundle" and "bundle
isomorphism". One definition: a bundle is a continuous projection-valued map,
isomorphism is `MvNEquiv` from L0. `found-bundle-calculus` must **import**
`Analysis/ProjectionMvNEquivalence.lean` rather than define its own equivalence
— and once it does, its homotopy invariance and its
trivialization-over-contractible are (L2) and (L3), already proved.

**C5 — clutching.** `found-bundle-calculus` owns the general clutching
construction over a closed cover; `lix-clutching` instantiates it for
`S⁵ = D₊ ∪ D₋`, and `found-ktheory-bott` uses the same construction for the Bott
class on `S²`/`S⁶`. Do not build three.

**C6 — the mapping torus.** Belongs to `found-bundle-calculus` (L1), because it
is a clutching construction and because L1 also owns the lemma of §B.7 that
makes it canonical. `found-euler-class` and `found-mapping-torus-parity` consume
it.

**C7 — `ch` versus `c`.** Define `ch` in `found-chern-classes`, as Newton
polynomials in the `c_i`, so that `k!·ch_k = p_k` is integral **by
construction**. `found-ktheory-bott` then only proves `ch` is additive on `K⁰`
and computes the `S^{2n}` normalization. If it defines its own `ch` from Chern
roots, the Newton integrality has to be reproved.

### C.4 Interfaces — L0 and L1

```lean
-- Analysis/ProjectionMvNEquivalence.lean            [lix-spaces]
def MvNEquiv {A : Type*} [CStarAlgebra A] (p q : A) : Prop :=
  ∃ w : A, star w * w = p ∧ w * star w = q
theorem MvNEquiv.refl / .symm / .trans
theorem MvNEquiv.add_of_orthogonal        -- p₁⊥p₂, q₁⊥q₂ → p₁+p₂ ~ q₁+q₂
theorem mvnEquiv_of_norm_sub_lt_one       -- (L1)
theorem mvnEquiv_of_path                  -- (L2)
theorem mvnEquiv_const_of_contractible    -- (L3)

-- Analysis/CornerCStarAlgebra.lean                  [lix-spaces]
def Corner (A) [CStarAlgebra A] (p : A) : Type := {x : A // p * x = x ∧ x * p = x}
noncomputable instance (hp : IsStarProjection p) (hp0 : p ≠ 0) : CStarAlgebra (Corner A p)
lemma Corner.mem_unitary_iff / Corner.mem_U0_iff

-- Topology/ConcreteSpaces.lean                      [lix-spaces]
def Sph (n : ℕ) / def CPd (d : ℕ) / def Gr (n N : ℕ) / def BaseSpace
instance : CompactSpace (CPd d) / (Gr n N) / (BaseSpace d)
def conjTaut (d : ℕ) : C(CPd d, Matrix (Fin (d+1)) (Fin (d+1)) ℂ)   -- q ↦ q̄, = O(1)

-- Topology/BundleProj.lean                          [found-bundle-calculus]
structure VBundle (X : Type*) [TopologicalSpace X] [CompactSpace X] where
  amb  : ℕ
  proj : C(X, CStarMatrix (Fin amb) (Fin amb) ℂ)
  isProj : ∀ x, IsStarProjection (proj x)
def VBundle.rank / .sum / .tensor / .dual / .pullback (f : C(Y,X))
def VBundle.Iso (E F : VBundle X) : Prop      -- MvNEquiv after padding to a common amb
theorem VBundle.iso_pullback_of_homotopic     -- from (L2)
theorem VBundle.trivial_of_contractible       -- from (L3)
def VBundle.clutch  (closed cover, ContinuousMap.liftCover')
def VBundle.mappingTorus (E : VBundle M) (g : unitary (End E)) : VBundle (Sph 1 × M)
theorem VBundle.exists_mappingTorus           -- §B.7: W|slice ≅ V → ∃ g, W ≅ W_g
```

### C.5 Interfaces — L2 to L6

```lean
-- Topology/SingularCohomologyRing.lean              [found-cohomology-ring]
H (R) (X) (n) : Type          -- graded, ring under cup
theorem H.pullback_ringHom / .homotopy_invariant / .mayer_vietoris
theorem H.sphere : H ℤ (Sph n) k ≅ if k = 0 ∨ k = n then ℤ else 0
theorem H.kunneth_of_free      -- free-case external product iso
def H.topPairing (X) : H ℤ X (dim X) ≃+ ℤ        -- via the Künneth generator, NO Poincaré duality

-- Topology/CPnCohomology.lean                       [found-cpn-cohomology]
def h (d : ℕ) : H ℤ (CPd d) 2
theorem cpn_ring : H ℤ (CPd d) ≅ ℤ[X]/(X^(d+1))
theorem cpn_odd_vanishing : H ℤ (CPd d) (2k+1) = 0
theorem prod_cpn_ring / prod_cpn_topGenerator

-- Topology/ChernClasses.lean                        [found-chern-classes]
def chern (E : VBundle X) (i : ℕ) : H ℤ X (2*i)
theorem chern_natural / chern_whitney / chern_line_eq_h / chern_of_iso
theorem splitting_principle
def totalChern (E) : H ℤ X            -- unit; def chernOfDiff (W V) := c W * (c V)⁻¹
def newton (i : ℕ) : H ℤ X (2*i)      -- p_i, integral polynomial in the c_j
def ch (E : VBundle X) : H ℚ X        -- Σ rank + p_i / i!
theorem ch_add / ch_mul / ch_natural
theorem newton_eq_factorial_smul_ch : (i ! : ℚ) • ch_i E = (newton i E : H ℚ X)

-- Topology/EulerClass.lean                          [found-euler-class]
theorem euler_eq_topChern (E : VBundle X) (h : E.rank = n) : e E = chern E n
theorem topPairing_eq_one_of_unique_nondegenerate_zero    -- ⟨e E, [N]⟩ = ±1

-- Topology/KTheoryBott.lean                         [found-ktheory-bott]
def KZeroTop (X) := KZero (C(X, ℂ))      -- from ktheory-k1
theorem ch_bott_sphere : ch_n '' (K̃ (Sph (2*n))) = (⊤ : Set ℤ)
theorem kt_min                            -- (KT-min) of §B.3

-- Topology/MappingTorusParity.lean                  [found-mapping-torus-parity]
theorem mappingTorus_topChern_even
    (Y even-cell) (V := 1³ ⊕ H) (g : unitary (End V)) :
    2 ∣ topPairing (chern (mappingTorus V g) r)          -- manuscript Lemma 3
```

### C.6 Interfaces — the five LIX lanes

```lean
-- ProblemLIXSpaces.lean                             [lix-spaces]
def Hproj / Eproj {l} (d : Fin l → ℕ) : CStarMatrix (Fin (rk d)) (Fin (rk d)) C(BaseSpace d, ℂ)
def blockAlg {l} (d) : Type := Corner _ (Eproj d)      -- A_i
noncomputable instance : CStarAlgebra (blockAlg d)

-- ProblemLIXClutching.lean                          [lix-clutching]
def Fproj : C(Sph 5, CStarMatrix (Fin 3) (Fin 3) ℂ)        -- x ↦ 1 - x xᴴ
def Dplus / Dminus, lemma contractible_D, lemma exists_frame        -- via (L3)
noncomputable def u : C(Sph 4, CStarMatrix (Fin 2) (Fin 2) ℂ)
theorem diag_u_one_mem_U0                                   -- §B.6 Removal 2
theorem mvnEquiv_clutch_of_mem_U0                           -- Corollary 4

-- ProblemLIXObstruction.lean                        [lix-obstruction]
theorem twistedCancellationFailure {l} (d : Fin l → ℕ) (hd : ∀ j, 0 < d j) :
    ¬ MvNEquiv (blockDiag (Fproj ⊗ 1) (Hproj' d)) (blockDiag 1₂ (Hproj' d))
theorem w_notMem_U0 {l} (d) : (w d) ∉ pathComponentOne (unitary (blockAlg d))
-- NOTE: in revision 1 the first of these was a named Prop. Under the new
-- mandate it is a THEOREM, proved from found-euler-class (odd side) and
-- found-mapping-torus-parity (even side).

-- ProblemLIXFiniteStage.lean                        [lix-limit]  (zero dependencies — start here)
theorem mem_U0_of_mem_U0_of_isDirected                      -- manuscript Lemma 7

-- ProblemLIXLimit.lean                              [lix-limit]
noncomputable def phi (i) / def limitAlg / instance : CStarAlgebra limitAlg
theorem limitAlg_isSimple / _stablyFinite / _separable / _unital / _infiniteDimensional
theorem v_homotopic_w                                       -- manuscript Lemma 6

-- Analysis/KOneUnitary.lean, KZeroProjection.lean   [ktheory-k1]
def stablyNull / def KOne / def K1Injective
theorem not_k1Injective_of_stablyNull_of_notMem_U0

-- ProblemLIX.lean                                   [lead wires]
theorem exists_simple_unital_not_k1Injective :
    ∃ (A : Type) (_ : CStarAlgebra A), IsSimpleCStar A ∧ ¬ K1Injective A
```

`limitAlg`: Mathlib has no inductive limit of C\*-algebras and building the
general theory is a trap. Realize every `A_i` concretely inside one fixed
containing C\*-algebra and define `limitAlg` as the closure of an increasing
union of `StarSubalgebra`s; then `ProblemLIXFiniteStage` applies verbatim.

---

## (D) Ledger

Revision 1's ledger listed what would remain a named `Prop`. Under the new
mandate that column is empty by construction, so this section instead records,
per layer, **what is owed and what is hard**, so that at any moment the campaign
can say exactly which layer is unfinished.

| Layer | Owed | Hardness |
|---|---|---|
| L0 | `MvNEquiv` calculus, corners, concrete spaces, `K₀`/`K₁` of a C\*-algebra | routine; ~1200 lines; no research content |
| L1 | bundle calculus in the projection model | routine given L0; `⊗` and the mapping torus are the only new constructions |
| L2 | cohomology ring, Künneth, top pairing | **large**, but mostly already vendored (C1); the new work is the ring structure, Künneth, and coefficient generality |
| L3 | `H^*(CP^n;ℤ)` and products | moderate; cell structure or Gysin, then Künneth |
| L4 | Chern classes | **the critical path.** Projective bundle formula + Leray–Hirsch is the single largest genuinely new piece |
| L5a | Euler class, one-zero count | moderate; Thom class and localization, no transversality theory |
| L5b | (KT-min) | **the deepest theorem in the campaign.** Bott periodicity (only for the `S^{2n}` normalization) plus Künneth for `S¹×S⁵×Y` |
| L6 | Lemma 3 | short once L4 and L5b are in: the argument is §B.3(b), a few hundred lines |
| L7 | the five LIX lanes | elementary C\*-algebra; ~4000–6000 lines; no research content |

**Where the campaign can still fail.** Two places, and only two.

1. **L5b.** Bott periodicity has never been formalized in Lean. The
   Atiyah–Bött clutching-function proof is self-contained and is the one to
   attempt; the target is narrow (`ch(K̃(S^{2n})) = ℤ`, not the full periodicity
   theorem as a natural equivalence), which is a real reduction, but it remains
   the single highest-risk item. If it stalls, the campaign stalls there and
   nowhere else — every other layer is independent of it except L6.
2. **L4's Leray–Hirsch.** The projective bundle formula needs
   `H^*(P(E))` free over `H^*(X)` with basis `1, ξ, …, ξ^{n-1}`, proved by
   Mayer–Vietoris induction over a finite trivializing cover. In the projection
   model `P(E) = {(x, q) : q a rank-one projection ≤ p(x)}` is concrete, which
   helps, but the induction is delicate.

**What is *not* at risk.** All of L0, L1, L3, L5a, L6 and L7, and the elementary
half of the manuscript (simplicity, stable finiteness, Lemma 6, Lemma 7, the
witness `u`, its stable triviality, clutching, `K₁` and `K1Injective`).

**Endpoint discipline.** `exists_simple_unital_not_k1Injective` becomes a closed
endpoint only when every layer above it is green. Until then it does not exist
as a theorem: under the new mandate there is no residue `Prop` to hypothesise on,
so the endpoint is simply unlanded, and must not be registered in the
endpoint/audit roster or cited in the manuscript.

**Superseded.** Revision 1's `TwistedCancellationFailure : Prop` and the
reduction theorem `not_k1Injective_of_twistedCancellationFailure` are withdrawn.
`lix-obstruction` proves the statement instead of naming it (§C.6).
