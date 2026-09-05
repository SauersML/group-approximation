# Lean route design for STW Problem LIX (target 3)

Architect's design for formalizing
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`
**fully unconditionally, with no residue**. Mathlib pin `81a5d257` (toolchain
v4.32.0); every Mathlib name below was checked at that revision with
`git -C /Users/user/mathlib4 grep -n <pat> 81a5d257 -- Mathlib`.

**Revision 3** (2026-09-05, latest) is the current route: §B.9. Revision 2 is
superseded on the mathematics — it concluded that the integral Chern-character
route was forced and named Bott periodicity as the campaign's deepest risk.
Both are wrong for this tower; §B.9 proves Lemma 3 mod 2 with no K-theory and no
Bott. §§B.3–B.5 are retained as the record of that reasoning and of the two
removals in §B.6, which still stand.

Revision 2 (2026-09-05, earlier): the mandate changed from "find the cheapest
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

`F` over `S⁵ ⊂ ℂ³` is `x ↦ 1 - x xᴴ`. **Superseded in detail by what landed:**
this design said `Sph 5` inside `EuclideanSpace ℝ (Fin 6)` with an explicit
`ℝ⁶ ≅ ℂ³`; `lix-spaces` instead used
`STW59.sphereFive : Set (Fin 3 → ℂ) := unitVectors (Fin 3)`, which is the better
carrier for `F` and is the model that stands. `S⁴` is `sphereFour` in
`EuclideanSpace ℝ (Fin 5)`, which already agrees with the cohomology model. The
`ℝ⁶ ≅ ℂ³` of the original plan survives as the **bridge** of §C.3 C2, not as the
ambient space of `F`.

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

> **REVISION 3 SUPERSEDES THIS SECTION'S CONCLUSION.** Revision 2 concluded that
> mod-2 methods cannot prove Lemma 3 and that the integral (Chern-character /
> Bott) route was therefore forced. That conclusion is correct **for general
> `Y`** and wrong **for this tower**, and the dividing line is the parity of the
> `d_j`. See §B.9, which is now the campaign's route: mod-2 throughout, no
> Chern character, no Künneth over `ℤ`, and **no Bott periodicity**. The
> argument below is retained because it is what tells a lane which hypothesis it
> may not drop.

**Scope of this section.** What follows is an argument that the *mod-2 route
cannot replace the K-theoretic parity inside route 4*. It is not, and was never,
an argument that route 4 is obstructed. Revision 1's `Sq²` argument applied to
routes 1–3 — direct detection of `Ση` on a suspension, where cup products vanish
— and ruled out route 4 on **cost alone**. Route 4 does not detect `Ση` on a
suspension: it detects the same `ℤ/2` on `S¹ × S⁵ × Y`, which is not a
suspension and whose cohomology ring is large, and Chern classes see that
computation perfectly well. That is exactly why `Y = ∏CP^{d_j}` is in the
construction: over `S⁵` alone the class is invisible because `[F] = [1²]` in
`K⁰(S⁵)`. Route 4 is the route we build.

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
**This is a witness that the mod-2 data is insufficient, not a counterexample:**
`1/6` is not realizable by any `β ∈ K⁰(CP¹)`, since `h² = 0` there makes
`ch(L) = 1 + h` and every actual class integral. See §B.9's framing correction.

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

### B.9 THE ROUTE (revision 3): Lemma 3 mod 2, via Wu and instability

Work mod 2 on `N = S¹ × S⁵ × Y`. Write `A = γ(V) = γ(H)`, and
`γ(δ) = 1 + z·b` with `b = Σ_j b_j`, `b_j ∈ H^{2j}(Y;𝔽₂)`, `z = t x`.
Multiplication by `z` is injective by Künneth, so every relation may be read on
`Y` after stripping `z`. The quantity to kill is
```
c_r(W) = Σ_k A_{m-k} · b_k        (top degree; m = Σ_j d_j, r = m+3).
```

**Step 1 — only even `k` appear.** `A_n = 0` for every odd `n`. This needs only
that every `d_j` is **even**: mod 2, `(1+h_j)^{d_j} = (1+h_j²)^{d_j/2}` by one
application of Frobenius, so each factor is a polynomial in `h_j²` and the
product is supported in even degrees; `m` is even too. Hence `A_{m-k} = 0` for
odd `k`.

*(Sharper, and true but not needed: since `d_j = 2^{j+1}` are distinct powers of
two, uniqueness of binary representation makes the subset sums exactly the even
integers `0,2,…,m`, each `A_n` a single monomial, and `A² = 1` — so
`γ(δ) = γ(W)·A` with no power-series inversion. Carry the evenness lemma; keep
the sparsity as an optimization.)*

**Step 2 — every even-index `b` vanishes.** Stripping `z` from
`Sq^{2k} γ_i(δ) = C(i-1,k)·γ_{i+k}(δ)` with `i = j+3` gives
```
(*)   Sq^{2k} b_j = C(j+2, k) · b_{j+k}
```
legitimate because `Sq^a z = 0` for `a > 0` (`z` lies in `H⁶(S¹×S⁵)`, which is
top degree there), so Cartan gives `Sq^{2k}(z·b) = z·Sq^{2k}b`. Now apply the
**instability axiom** on `Y`: `b_j` has degree `2j`, so `Sq^{2k} b_j = 0`
whenever `k > j`. Therefore
```
k > j and C(j+2,k) odd   ⟹   b_{j+k} = 0,
```
and for every even `n ≥ 2` such a pair exists with the binomial equal to `1` on
the nose:
```
j = n/2 - 1,   k = n/2 + 1,   C(j+2,k) = C(n/2+1, n/2+1) = 1,   k > j.
```
So `b_n = 0` for every even `n ≥ 2`. With `b_0 = 0` — the base case:
`γ₁ = γ₂ = 0` by degree, and `Sq²γ₂ = γ₁γ₂ + γ₃` gives `γ₃ = 0` — every
even-index `b` vanishes.

**Conclusion.** Step 1 leaves only even `k`; step 2 kills every even-index `b_k`.
So `c_r(W) ≡ 0 mod 2` at every tower stage — no induction on `ℓ`, no case
analysis, no supplementary relation.

Spot checks: `n=2 → (0,2)`, `C(2,2)=1`, `Sq⁴b₀ = 0` since `4 > 0`;
`n=4 → (1,3)`, `C(3,3)=1`, `Sq⁶b₁ = 0` since `6 > 2`;
`n=6 → (2,4)`, `C(4,4)=1`, `Sq⁸b₂ = 0` since `8 > 4`.
A full Lucas enumeration of `(*)` gives zeros at
`n = 0,2,3,4,6,7,8,10,11,12,14,15,16,18,19,20,…`; the only unreachable indices
are `n ≡ 1 (mod 4)` — all odd, hence all invisible to an even-supported `A`.
That is why "the binomials fail for some `k`" and it does not matter.

**Why this reconciles §B.2.** §B.2's witness was `Y = CP¹`, where `γ₁ = 1/6`
satisfies every mod-2 constraint while `c₄(δ)` is odd. There `d = 1` is **odd**,
so `A = 1 + h` has odd-degree support and `m = 1` is odd; the sum is
`A₁b₀ + A₀b₁ = b₁`, and `b₁` has index `1 ≡ 1 (mod 4)` — precisely the
unreachable class. Both statements stand: mod 2 **cannot** prove Lemma 3 for
general `Y`, and **can** for this tower.

*Framing correction (team-lead).* `γ₁ = 1/6` is **not** a bundle-level
counterexample and the doc should not call it one. On `CP¹`, `h² = 0`, so
`ch(L) = e^h = 1 + h` and every actual class in `K⁰(CP¹)` has integral Chern
character; `1/6` is not realizable. What it exhibits is that **the mod-2 data
alone does not pin `c₄`** — an obstruction to the *method*, not to the
statement. That is exactly the claim §B.9 needs, and it shows the evenness
hypothesis doing real work rather than bookkeeping: the integral route proves
`c₄(δ)` even on `CP¹` *because of* that integrality, and the mod-2 route cannot.

### B.9.1 Two criteria, and which one is proved

`team-lead` derived a different and weaker-looking criterion, and the doc records
both because a reader given only one will be misled.

* **team-lead's.** `Sq²(c_i) = c_1c_i + (i-1)c_{i+1}`, so the instance producing
  `c_r` from `c_{r-1}` carries coefficient `r-2`, usable exactly when `r` is odd,
  i.e. when **`Σ_j d_j` is even**. (I confirmed the coefficient.)
* **§B.9's.** Step 1 needs **every `d_j` individually even**, which is strictly
  stronger: one Frobenius puts `A` in even degrees, and that fails as soon as a
  single `d_j` is odd, even when the sum is even.

Separating test case: `Y = CP¹ × CP¹`, `d = (1,1)`, `m = 2` even, `r = 5` odd.
team-lead's criterion says live; §B.9 does not apply, because
`A = (1+h₁)(1+h₂)` has odd-degree components, so the sum keeps
`A₁b₁ = (h₁+h₂)b₁` and `b₁` sits in the one residue class `n ≡ 1 (mod 4)` that
Step 2 cannot reach. So either the `r-2` route has an ingredient beyond the
coefficient that also handles odd `d_j`, or the true criterion is "all `d_j`
even". **The tower is in the good case under either reading** (`d_j = 2^{j+1}`,
individually even), so nothing operational turns on it — but the doc must record
the criterion `lix-obstruction` actually verified, not the weaker-looking one.

*One gap I could not reconstruct in the `r-2` route:* `γ_r = Sq²(γ_{r-1})`
exhibits the top class as a square but does not make it vanish. Evaluating on
`N` and applying Wu for the manifold turns it into `⟨v₂·γ_{r-1}, [N]⟩` with
`v₂ = w₂(TY) = Σ_j (d_j+1)h_j = Σ_j h_j` mod 2 when the `d_j` are even — not
obviously zero. §B.9 avoids that step entirely: it works on `δ` rather than `W`,
and uses **instability** rather than the manifold's Wu class. If the `r-2` route
needs `v₂·γ_{r-1} = 0`, that is a third item for the verification list.

**The hypothesis a lane may not drop is that every `d_j` is even** — and the
construction's doubling `d_j = 2^{j+1}`, which `lix-obstruction` showed is forced
by multiplicity matching, supplies it. That is why the doubling matters beyond
multiplicity matching, and it belongs in the manuscript's commentary.

*Resolved (team-lead, after re-deriving Step 2 independently).* The `r-2` route
is withdrawn: `γ_r = Sq²(γ_{r-1})` exhibits the top class as a square but does
not make it vanish, and `⟨v₂·γ_{r-1},[N]⟩` is not obviously zero. §B.9's
criterion — every `d_j` even — is the operative one; `Σ_j d_j` even is the
weaker condition the top-class Wu instance needs, implied and not binding.

### B.10 The Euler wall: the odd side, decomposed

`found-euler-class` cannot bridge "the section has exactly one transverse zero"
to "the top class is nonzero", and as stated they are right: that sentence *is*
the Thom isomorphism plus localization plus manifold theory. Stated mod 2 and
for our `N` only, it decomposes into four steps, three of which are cheap.

* **E1 — the relative top class. THE IRREDUCIBLE PIECE.** For a rank-`r` bundle
  `W` on a compact `X` and a section `s` nowhere zero on a closed `A ⊆ X`, a
  class `e(W,s) ∈ H^{2r}(X, A; 𝔽₂)`, natural in `(X,A)`, whose image in
  `H^{2r}(X;𝔽₂)` is `w_{2r}(W)`. This is the Thom class in disguise and there is
  no way around it.
* **E2 — excision and the top cell.** With `A = N ∖ int D` for a `2r`-disk `D`
  around the zero, excision gives
  `H^{2r}(N,A;𝔽₂) ≅ H^{2r}(D,∂D;𝔽₂) ≅ 𝔽₂`, and the map to `H^{2r}(N;𝔽₂) ≅ 𝔽₂`
  is an **iso**. Prove this **cellularly, not by manifold theory or Poincaré
  duality**: `N = S¹ × S⁵ × ∏CP^{d_j}` has an explicit product CW structure with
  a *unique* top cell, which may be chosen inside `D`, so the map is an iso by
  cellular cochain inspection — and the vendored tree already has the
  cellular↔singular comparison.
* **E3 — the relative class is the local degree.** `e(W,s)` corresponds under E2
  to `deg₂(s|_{∂D})`, where `s|_{∂D}` lands in `ℂ^r ∖ 0 ≃ S^{2r-1}`.
* **E4 — a nondegenerate zero has odd degree.** Mod 2 this is trivial: the
  derivative is a real-linear isomorphism and a linear iso induces a degree `±1`
  map of spheres. **Working mod 2 deletes all the orientation bookkeeping the
  manuscript carries** — its derivative `(ξ,a) ↦ ξ/2 - 2a e₃` only has to be
  invertible, never orientation-tracked. The vendored degree machinery covers
  this.

So the ask to `found-euler-class` is **E1 alone**, stated relatively and mod 2,
with E2–E4 as separate small lemmas — a much smaller target than "the Euler
class of an oriented bundle with its signed transverse-zero count".

*If E1 is unreachable*, it becomes the campaign's single named `Prop`, one layer
below and much smaller than the withdrawn `TwistedCancellationFailure`.

*On W4(i).* The instruction not to build Poincaré duality still stands for the
top pairing. But if E1 turns out to want a perfect cup pairing, note that for our
`N` that is pure algebra rather than manifold theory: `H^*(N;𝔽₂)` is a tensor
product of `𝔽₂[h]/(h^{d+1})`'s and sphere factors by Künneth, and perfectness of
the cup pairing on such a ring is a direct computation. Cheap if needed — still
not to be built speculatively.

**Wu for the virtual class — RESOLVED, and cheap.** Relation `(*)` applies Wu to
`δ`, where `γ(δ) := γ(W)·γ(p*V)^{-1}`. This needs no re-derivation of Wu for
formal differences. `w(E) = ∏(1+y_i)` with `y_i` the mod-2 Chern roots in degree
2; `Sq(y_i) = y_i + Sq¹y_i + y_i² = y_i + y_i²`, since `y_i` is the reduction of
an integral class and the Bockstein kills it; so `Sq(w(E)) = ∏(1+y_i+y_i²)`.
Both `Sq` and that universal expression are **multiplicative** on the group of
normalized total classes — `Sq` by Cartan, the expression because the roots of a
product are the union — and they agree on genuine bundles by the splitting
principle. Two group homomorphisms agreeing on a generating set agree on the
subgroup generated, which contains every formal quotient. So the Lean obligation
is Cartan, the `CommGroup` of normalized total classes, and
`Sq(1+y) = 1+y+y²`. `found-chern-classes`' `TotalChern` already supplies the
middle. *(Argument due to `team-lead`; verified here. This was revision 3's
top-listed risk and is now the cheapest item on the list.)*

Instability, Frobenius and the Künneth injectivity of `z` are cheap likewise.

**What B.9 deletes.** Bott periodicity, the Chern character, Newton's identity,
integral Künneth, integral Chern classes, the integral Euler class, and (KT-min)
in its entirety. `found-ktheory-bott` is repointed to **Steenrod squares up to
the Cartan formula and no further**; `found-mapping-torus-parity` to **Wu's
formula as symmetric-function algebra**; `found-chern-classes` to **mod-2 Chern
classes only**; `found-euler-class` to the **mod-2 Euler class only**. A
consequence already observed by `found-cohomology-ring`: its blocker — "every
subgroup of a free abelian group is free" at arbitrary rank, for the UCT
splitting — **evaporates over `𝔽₂`**, since a subspace of a vector space is free
with no transfinite argument. That detour and its proposed extra lane are
cancelled.

**Fallback, kept in markdown only (per `audit-gate`).** If B.9 stalls, the
statement to fall back to is
```lean
/-- Manuscript Lemma 2, as Murray–von Neumann inequivalence. -/
TwistedCancellationFailure : Prop :=
  ∀ {l} (d : Fin l → ℕ), (∀ j, 0 < d j) →
    ¬ MurrayVonNeumannEquiv (blockDiag (Fproj ⊗ 1) (Hproj' d)) (blockDiag 1₂ (Hproj' d))
```
It lives here and **nowhere in the Lean tree**: a `Prop` in a markdown file
cannot reach an audit roster, and deleting it would cost the campaign its honest
fallback for nothing.

---

## (C) The cross-lane graph

### C.1 Layers

| Layer | Module | Owner | Contents |
|---|---|---|---|
| L0 | `Analysis/FiniteCStarMurrayVonNeumann.lean` **(landed)** | `lix-spaces` | `MurrayVonNeumannEquiv` (:99) and its calculus; (L1)(L2)(L3) are **re-homed here** from `AlgTop/BundleCalculusProjection.lean` — see C8 |
| L0 | `Analysis/LIXCornerAlgebra.lean` **(landed)** | `lix-spaces` | `SectionAlgebra`, `cornerAlgebra`, `Corner`, `cornerOne`, `corner_complete`, `ofFunctionMatrix` |
| L0 | `Analysis/LIXProjectiveSpaceModel.lean` **(landed)** | `lix-spaces` | `cpSet` (:402), `CP d` (:471), `rankOneProj`, `eq_rankOneProj_of_trace_one`, compactness |
| L0 | `Topology/ConcreteSpaces.lean` | `lix-spaces` | only what is **not** landed: `Sph n`, `Gr n N`, `BaseSpace`, `ℝ^{2k} ≅ ℂ^k` |
| L0 | `Analysis/KOneUnitary.lean` | `ktheory-k1` | `K₁` of a C\*-algebra |
| L0 | `Analysis/KZeroProjection.lean` | `ktheory-k1` | `K₀` of a C\*-algebra |
| L1 | `Topology/BundleProj.lean` | `found-bundle-calculus` | bundle = projection; rank, `⊕`, `⊗`, dual, pullback; `Iso := MvNEquiv`; homotopy invariance; clutching over a closed cover; mapping torus |
| L2 | `Topology/SingularCohomologyRing.lean` | `found-cohomology-ring` | graded ring `H^*(−;R)`, naturality, homotopy invariance, Mayer–Vietoris, `H^*(Sⁿ)`, free-case Künneth, top-class pairing |
| L3 | `Topology/CPnCohomology.lean` | `found-cpn-cohomology` | `H^*(CPd d;ℤ) ≅ ℤ[h]/(h^{d+1})`; products; the Künneth generator |
| L4 | `Topology/ChernClasses.lean` | `found-chern-classes` | **mod-2 only**: `γ_i = c_i mod 2` (= `w_{2i}`), Whitney, splitting principle, naturality, `γ(δ) = γ(W)γ(V)^{-1}`. No integral Chern classes, no `ch`, no Newton |
| L5a | `Topology/EulerClass.lean` | `found-euler-class` | **mod-2** Euler class `= w_top`; one nondegenerate zero ⟹ odd count |
| L5b | `Topology/SteenrodSquares.lean` | `found-ktheory-bott` **(repointed)** | cup-`i` products, `Sq^i`, Cartan, instability. **No K-theory, no Bott, no `ch`** |
| L6 | `Topology/MappingTorusParity.lean` | `found-mapping-torus-parity` | Wu's formula as symmetric-function algebra, then §B.9 |
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
| `MurrayVonNeumannEquiv`, (L1)(L2)(L3), `UnitaryConj` | `Analysis/FiniteCStarMurrayVonNeumann.lean` | imports; **no second MvN predicate anywhere** |
| `MurrayVonNeumannEquiv.trans`, `.map` | `KTheory/MatrixProjection.lean` (:78, :99) | imports; `BundleCalculus` deletes its versions |
| `blockSum` = the campaign's `⊕`, and its calculus | `KTheory/{MatrixProjection,BlockMoves}.lean` | imports; never restated on `CStarMatrix` |
| `KOne`/`KZero`, stated for an **arbitrary** C\*-algebra | `ktheory-k1` | `BundleAlg X N` is the instantiation `A := C(X,ℂ)` |
| `Corner p A p` | `Analysis/LIXCornerAlgebra.lean` | imports |
| `CP d`, `cpSet d` | `Analysis/LIXProjectiveSpaceModel.lean` (namespace `GroupApproximation.STW59`) | imports, never redefines; `AlgTop.CPn` is its lemma layer |
| `sphereFive` (S^5, in `Fin 3 -> C`), `sphereFour` (S^4, Euclidean) | `Analysis/LIXBlockProjections.lean` | imports |
| `sphereFiveHomeoSphere` — the ONE bridge to `SphereOddDegree.Sphere 5` | `Topology/SphereModelBridge.lean` (`lix-spaces`, owed) | the only LIX-side importer of `SphereOddDegree` |
| `Gr n N` | `lix-spaces` | not yet claimed |
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

**C2 — the sphere model. NOW LIVE, and RULED: bridge, do not unify.**
Revision 3 recorded this as not yet live. It is live, for exactly one space.

* `STW59.sphereFive : Set (Fin 3 → ℂ) := unitVectors (Fin 3)`
  (`Analysis/LIXBlockProjections.lean:117`) carries `F`, `hopfCol` and every
  block projection.
* `SphereOddDegree.Sphere n := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)`
  (`SphereOddDegree/Basic.lean:19`) carries the whole `AlgTop` cohomology stack
  (`CupProduct`, `CupAssoc`, `CrossProduct`, `SingularCohomology`,
  `SingularChainFree`, `CochainLeibniz`, `OddDegreeOfHomeomorphism`).

`EuclideanSpace ℝ (Fin 6)` is `PiLp 2`, distinct from `Fin 6 → ℝ`, distinct
again from `Fin 3 → ℂ`; nothing bridges them, and no `LIX*` module imports
`SphereOddDegree` at all.

**The decisive fact:** in the same file, `sphereFour` (:114) is
`Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1`, *definitionally*
`SphereOddDegree.Sphere 4`. So `lix-spaces` did not adopt a rival convention —
`S⁴` is already on the cohomology model and only `S⁵` diverged, because
`F(x) = 1 - xxᴴ` needs `x` to be a complex vector. One space, not a fault line.

**Ruling.** Bridge. Restating `sphereFive` as `Sphere 5` would put a conversion
at every use of `F`, `hopfCol` and every block projection, permanently; bridging
puts one at a handful of joins. The asymmetry is that cohomology is a *homotopy
functor* and transports across a homeomorphism for free, while `1 - xxᴴ`
transports across nothing. `lix-spaces` lands
`GroupApproximation/Topology/SphereModelBridge.lean` with the single declaration
```lean
STW59.sphereFiveHomeoSphere : ↥STW59.sphereFive ≃ₜ SphereOddDegree.Sphere 5
```
Cheaper than it looks: `Topology/OddMapNormalization.lean:80` already has
`realToComplex n : EuclideanSpace ℝ (Fin (2n+2)) → (Fin (n+1) → ℂ)` with
continuity (:84) and injectivity proved, and at `n = 2` that is exactly the map.
Missing: the norm identity `∑ i, ‖realToComplex 2 x i‖² = ‖x‖²` (from
`‖a+bI‖² = a²+b²`, i.e. `Complex.sq_abs` plus one reindexed sum), which is what
carries `Metric.sphere 0 1` onto `unitVectors (Fin 3)` — defined by that same
equation; then surjectivity; then `Continuous.homeoOfEquivCompactToT2`, so **no
inverse need be constructed**. Both compactness instances already exist.

**The discipline that makes the fork harmless.** A bridge alone only defers the
failure mode: both halves keep compiling green about different spaces until
someone remembers to transport. So **every cohomology fact consumed on the
C\*-side must be STATED over `sphereFive`**, obtained once through the bridge.
Auditable form (phrasing refined by `audit-gate`, and adopted): **no
`Analysis/LIX*` or `KTheory/*` module may import `SphereOddDegree` except
through `SphereModelBridge`.** My earlier "LIX-side" was ambiguous — `AlgTop/*`
legitimately imports it for `CupProduct`, `SingularCohomology`, `CrossProduct`
and the rest, and would have been caught by the loose phrasing. `audit-gate`
measured the current state as a genuine **zero** such imports, so the invariant
is enforced from a clean baseline rather than a grandfathered set.

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

**C8 — two Murray–von Neumann predicates, both already landed. RESOLVED.**
`Analysis/FiniteCStarMurrayVonNeumann.lean:99` and
`AlgTop/BundleCalculusProjection.lean:68` define
`∃ v, star v * v = p ∧ v * star v = q` character-for-character, under the same
typeclass assumptions, in different namespaces, and the second does not import
the first. `cairn`'s duplicate detector cannot see this.

*Ruling:* `MurrayVonNeumannEquiv` survives. It is older and already consumed by
`KTheory/MatrixProjection.lean`, `Analysis/LIXCornerAlgebra.lean`,
`Analysis/CoronaProjectionOrder.lean`, `Analysis/OmegaFiniteComparison.lean`,
`Analysis/MFStablyFinite.lean` and four `OneSidedMFRadical` manuscript files, so
renaming it would touch the manuscript corpus while renaming the newer one
touches one lane. `BundleCalculusProjection.lean` imports it, deletes its own
`def MvNEquiv`, drops `MvNEquiv.refl`/`.symm` in favour of the existing ones,
and re-homes onto `MurrayVonNeumannEquiv` its genuine additions: `UnitaryConj`
(:73), `UnitaryConj.mvNEquiv` (:103), and the three analytic lemmas
`mvNEquiv_of_norm_sub_lt_one` (:277), `unitaryConj_of_preconnected` (:288) and
`mvNEquiv_of_path` (:349) — which are exactly (L1), (L3) and (L2).

*Correction (raised by `found-ktheory-bott`).* `.trans` is **not** among the
re-homed lemmas. `KTheory/MatrixProjection.lean:78` already declares
`MurrayVonNeumannEquiv.trans` under `[Semigroup A] [StarMul A]` with
`IsIdempotentElem` at both ends — strictly weaker hypotheses than
`BundleCalculusProjection.lean:131`, which asks `IsStarProjection` at both ends
in a C\*-ambient. Only idempotence of the two ends is used, since `w * v`
implements the composite. Likewise `MurrayVonNeumannEquiv.map` (:99). **Ruling:**
`KTheory/MatrixProjection.lean` owns `.trans` and `.map`; `BundleCalculus`
**deletes** rather than re-homes those two, and imports that file.

**C10 — the direct sum. RESOLVED before it surfaced.**
`KTheory/MatrixProjection.lean:122–216` and `KTheory/BlockMoves.lean` already
hold `blockSum` with a complete calculus: `blockSum_mul_blockSum`,
`star_blockSum`, `isStarProjection_blockSum`, `murrayVonNeumannEquiv_blockSum`,
`murrayVonNeumannEquiv_submatrix`, `blockSum_submatrix`, `blockSum_comm`,
`blockSum_assoc`, `blockSum_zero_right`, and the reindexing equivalences
`finSumCongr`, `finSumSwap`, `finSumAssoc`. That is exactly the `⊕` named in
`found-bundle-calculus`'s mandate. **Ruling:** `⊕` lives in
`GroupApproximation.KTheory`; `found-bundle-calculus` consumes it and does not
restate it on `CStarMatrix`.

**C11 — the model seam, and where the K-groups are stated.** `blockSum` lives on
`Matrix (Fin m) (Fin m) A` over a bare `[NonUnitalSemiring A] [StarRing A]`;
`found-bundle-calculus` pinned `BundleAlg X N := CStarMatrix (Fin N) (Fin N) C(X,ℂ)`.
**Ruling:** the block calculus stays typeclass-minimal — it contains no analysis
and must not acquire a C\*-typeclass to reach `BundleAlg` — and **the K-groups
are stated in the general algebraic model, for an arbitrary C\*-algebra `A`, not
over `BundleAlg`.** That is forced by §C.7: the Problem LIX endpoint must be
stated over a generic `KOne`, and a `KOne` defined over `BundleAlg X N` could not
carry it. `BundleAlg X N` is the instantiation `A := C(X,ℂ)`.

The seam is nearly free: at the pin `CStarMatrix` is a **type synonym** —
`def CStarMatrix (m n A) := Matrix m n A` (`CStarMatrix.lean:44`) with
`def ofMatrix : Matrix m n A ≃ CStarMatrix m n A := Equiv.refl _` (:54) — so one
transfer lemma at `BundleAlg` suffices and every `blockSum` lemma transports by
`rfl` or a one-line `simp [ofMatrix]`.

*Consequence for the plan:* **L0's analytic floor is already done.** Revision 2
listed (L1)(L2)(L3) as unbuilt; they are built, on the wrong predicate.
`Analysis/ProjectionMvNEquivalence.lean` and `Analysis/CornerCStarAlgebra.lean`
are **withdrawn** — they were proposed from a Mathlib grep that was never
repeated against this repository.

**C9 — `IsLineProj` is undefined repo-wide.** There is no rival `CP^d` model:
`AlgTop/ComplexProjectiveBasic.lean` imports `Analysis/LIXProjectiveSpaceModel`
and opens `GroupApproximation.STW59`, defining no type, and the only `cpSet`/`CP`
in the repository are STW59's, already built on Mathlib's `IsStarProjection`
with the trace clause — the program note's model exactly. But `IsLineProj` has
four occurrences repo-wide and **no definition**:
`AlgTop/ComplexProjectiveHyperplane.lean:39,40,69` and
`AlgTop/ComplexProjectiveChart.lean:49`. Those files were written against a
planned bespoke structure — note the dot-notation `h.col_eq_zero_of_diag_eq_zero`,
`h.conj_entry` — while the landed base uses `IsStarProjection`. They must be
ported onto `ComplexProjectiveBasic`'s lemmas (`col_eq_zero_of_diag_eq_zero`
:64, `row_eq_zero_of_diag_eq_zero` :76, `entry_symm` :109, `minor` :87) before
any more of the cell decomposition is built on them. No new predicate.

*Why no gate caught it:* the lakefile sets only
`moreLeanArgs = ["-DwarningAsError=true"]` for the `GroupApproximation` lib and
does not set `autoImplicit := false`, so an unresolved identifier in hypothesis
position auto-binds instead of erroring.

### C.4 Interfaces — L0 and L1

```lean
-- Analysis/FiniteCStarMurrayVonNeumann.lean  [LANDED; (L1)(L2)(L3) re-homed here per C8]
def MurrayVonNeumannEquiv {A} [Mul A] [Star A] (p q : A) : Prop :=
  ∃ v : A, star v * v = p ∧ v * star v = q          -- :99
theorem MurrayVonNeumannEquiv.refl / .symm          -- :104, :114;  .trans from C8
def UnitaryConj / theorem UnitaryConj.mvNEquiv      -- from C8
theorem mvNEquiv_of_norm_sub_lt_one                 -- (L1), from C8
theorem mvNEquiv_of_path                            -- (L2), from C8
theorem unitaryConj_of_preconnected                 -- (L3), from C8
-- still owed: MurrayVonNeumannEquiv.add_of_orthogonal (block sums)

-- Analysis/LIXCornerAlgebra.lean                    [LANDED]
abbrev SectionAlgebra (X) (ι) / def cornerAlgebra / abbrev Corner / instance cornerOne
theorem corner_complete / ofFunctionMatrix / murrayVonNeumannEquiv_ofFunctionMatrix
-- still owed: the CStarAlgebra instance on Corner, and Corner.mem_unitary_iff/mem_U0_iff

-- Analysis/LIXProjectiveSpaceModel.lean             [LANDED]
def cpSet (d) := {q | IsStarProjection q ∧ q.trace = 1}      -- :402
abbrev CP (d) := ↥(cpSet d)                                  -- :471
def rankOneProj / theorem eq_rankOneProj_of_trace_one / cpSet_eq_image / isCompact_cpSet

-- AlgTop/CPTautologicalSection.lean                 [LANDED — this is §A.1's O(1) section]
def dualTautSection (x : CP d) : Fin d → Fin (d+1) → ℂ
theorem dualTautSection_eq_zero_iff / dualTautSection_zeroLocus   -- exactly one zero

-- Topology/ConcreteSpaces.lean                      [lix-spaces — only the unclaimed part]
def Sph (n : ℕ) / def Gr (n N : ℕ) / def BaseSpace
instance : CompactSpace (Gr n N) / (BaseSpace d)

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

### C.7 The endpoint lands FIRST (gating requirement on `ktheory-k1`)

Raised by `audit-gate` and accepted as a hard requirement. The named `Prop` that
**is** Problem LIX must land *before* anything is proved about it, and must be
stated over Mathlib vocabulary plus a generic `KOne` — never over a definition
introduced by the counterexample's own construction. An endpoint whose statement
is written after the proof, in the proof's vocabulary, cannot be audited from
outside.

```lean
/-- STW Problem LIX: is every unital simple C⋆-algebra K₁-injective? -/
def ProblemLIX : Prop :=
  ∀ (A : Type) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A],
    Nontrivial A → IsSimpleCStar A → K1Injective A
```

**The typeclass wrinkle, and why it is not one.** `[PartialOrder A]` and
`[StarOrderedRing A]` are **forced by Mathlib**, not gratuitous: at the pin every
`CStarMatrix` instance sits under
`[NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]`
(`Analysis/CStarAlgebra/CStarMatrix.lean`, the `NonUnital` section), so
`CStarMat n A` cannot be formed without them, and `K1Injective` inherits them.
This *looks* like quantifying over a choice of order, which would weaken
`¬ ProblemLIX`. It does not: `StarOrderedRing` pins the order completely, since
it characterises `x ≤ y` by `y - x` lying in the additive closure of
`{star s * s}`, so any two such structures on the same starred ring coincide.
Worth landing as a one-line lemma rather than leaving a reader to reconstruct
— and `audit-gate` sharpens the reason: Lean's elaborator does not know this, so
`K1Injective A` at two propositionally equal instances is two distinct terms, and
an argument in a design doc is available neither to the kernel nor to a referee.
The relation is characterised at `Mathlib/Algebra/Order/Star/Basic.lean:79`:
`le_iff : ∀ x y, x ≤ y ↔ ∃ p ∈ AddSubmonoid.closure (Set.range fun s => star s * s), y = x + p`.

**Universe.** `KOne : Type u` is universe-polymorphic (`CStarKOne.lean:32`,
`:65`), so quantifying over `Type` is genuinely weaker than over `Type u`.
`Type` is the right choice — the witness is concrete and separable, built from
matrices over `C(X,ℂ)`, so it lives in `Type 0` — but it must be a *recorded*
choice in the docstring, not an artefact of what the author typed first.
Contrast target 1, where `.{1}` is *structurally forced* because
`MaximalGroupCStar` raises the level; here the choice is free, and a free choice
recorded as a choice is the difference between a decision and an artefact.

`K1Injective A` is defined for an **arbitrary** unital C\*-algebra as injectivity
of `unitary A ⧸ Subgroup.pathComponentOne (unitary A) → KOne A`, where `unitary`
is Mathlib's (`Algebra/Star/Unitary.lean:35`) and `Subgroup.pathComponentOne` is
Mathlib's (`Topology/Connected/PathConnected.lean:375`, with the C\*-specific
`Unitary.mem_pathComponentOne_iff` at
`Analysis/CStarAlgebra/Unitary/Connected.lean:336`). `KOne` is new — Mathlib has
no C\*-K-theory at the pin — but it must be generic: no mention of the
counterexample, its spaces, or its projections. The target is `¬ ProblemLIX`.

**Status.** The K-theory half is **landed and generic** — `audit-gate` measured
it across `Analysis/{CStarKOne, CStarKOneInjectivityCriterion,
CStarUnitaryComponent, SequentialGroupColimit}` and `KTheory/*` and found zero
counterexample-specific names in any declaration, with
`CStarUnitaryComponent` and `SequentialGroupColimit` importing only Mathlib. I
checked the declarations and confirm it. Real signatures:

```lean
Analysis/CStarUnitaryComponent.lean:79   unitaryComponentOne A : Subgroup (unitary A)
                                           := Subgroup.pathComponentOne (unitary A)
Analysis/CStarUnitaryComponent.lean:126  abbrev UnitaryClass A := unitary A ⧸ unitaryComponentOne A
Analysis/CStarKOne.lean:65               abbrev KOne : Type u := (kOneTower A).Colim
Analysis/CStarKOne.lean:111              def kappa : UnitaryClass A →* KOne A
Analysis/CStarKOne.lean:118              def K1Injective : Prop := Function.Injective (kappa A)
Analysis/CStarKOneInjectivityCriterion.lean:84,97,105
     not_k1Injective_of_diagOne_mem / _of_joined_diagOne / _of_exists_witness
```
An earlier revision of this section warned that `KOne` might have been shaped
around the counterexample. It was not; that is recorded here as a **pass**, in
the detail a failure would have had.

**`ProblemLIX` is still unstated, and the blocker is a missing simplicity
predicate.** There is no `IsSimpleCStar`: grepping every
`def/abbrev/structure/class` matching `*[Ss]imple` across `GroupApproximation`
returns only `IsPurelyInfiniteSimpleUnitalRing` (manuscript-local,
`OneSidedMFRadical/PartialClosureAnalysis.lean:601`), one use of Mathlib's
`IsSimpleGroup`, and Choquet/Bauer simplex material — nothing about closed
two-sided ideals of a C\*-algebra. So the endpoint is one small generic
definition away, and **that definition must land before
`ProblemLIXLimit.lean`'s simplicity theorem**: written afterwards it is exactly
the kind that gets shaped to fit the specific limit. `IsSimpleCStar` landing
after the simplicity proof is the same failure mode as the endpoint landing
after the refutation.

**The `IsSimpleRing` trap (raised by `audit-gate`).** Mathlib at the pin has
`IsSimpleRing R : Prop` = `IsSimpleOrder (TwoSidedIdeal R)`
(`RingTheory/SimpleRing/Defs.lean:27`) — *algebraic* two-sided ideals, no closure
condition — and it is the obvious shortcut for whoever writes `IsSimpleCStar`.
It is the wrong notion to state, and the direction of the danger is the reverse
of the usual one: since `ProblemLIX = ∀ A, IsSimple A → K1Injective A`,
strengthening `IsSimple` makes `¬ ProblemLIX` **harder**, not vacuous.

*But the two notions coincide here, and the severity claim does not survive.*
In a unital Banach algebra a proper two-sided ideal `J` contains no unit, so
`J ⊆ nonunits`; Mathlib supplies
`nonunits.subset_compl_ball : nonunits R ⊆ (Metric.ball (1:R) 1)ᶜ`
(`Analysis/Normed/Ring/Units.lean:84`) and `nonunits.isClosed` (:88), so
`1 ∉ closure J` and `closure J` is a proper closed two-sided ideal; C\*-simplicity
gives `closure J = 0`, hence `J = 0`. Mathlib's `CStarAlgebra` extends
`NormedRing` and is unital, so **for our `A`, C\*-simple ⟺ `IsSimpleRing`**. The
`K(H)` example that makes the general claim true — C\*-simple with the
finite-rank operators as a dense proper ideal — is non-unital.

So the failure mode is not "an endpoint nobody can discharge". It is (i)
**fidelity** — STW Problem LIX means C\*-simple, and an endpoint stated with
`IsSimpleRing` is not visibly the problem asked; and (ii) **a theorem smuggled
into a definition** — the equivalence needs unitality, and `lix-limit` will prove
the closed-ideal statement anyway, since the manuscript's positive-cutdown
argument (Lemma 5) produces closed ideals.

**Ruling.** Define `IsSimpleCStar` by **closed** two-sided ideals, and separately
land
```lean
theorem isSimpleCStar_iff_isSimpleRing (A) [CStarAlgebra A] [Nontrivial A] :
    IsSimpleCStar A ↔ IsSimpleRing A
```
from the two `nonunits` lemmas. It is short, it documents that the choice costs
nothing, and it forecloses the substitution.

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
| L2 | cohomology ring, Künneth, top pairing — **over `𝔽₂`** | **large**, but mostly already vendored (C1), and the UCT blocker evaporates over `𝔽₂` (§B.9) |
| L3 | `H^*(CP^n;𝔽₂)` and products | moderate; cell structure or Gysin, then Künneth |
| L4 | **mod-2** Chern classes `γ_i = w_{2i}`, Whitney, splitting principle | moderate. No projective bundle formula, no Leray–Hirsch, no `ch` |
| L5a | mod-2 Euler class, one-zero count | **THE WALL.** E1 (relative top class = Thom in disguise) is irreducible; E2–E4 are cheap. See §B.10 |
| L5b | Steenrod squares up to Cartan and instability | **the largest single new build.** Cup-`i` products via equivariant acyclic carriers. No K-theory, no Bott |
| L6 | Wu's formula, then §B.9 | short once L4 and L5b are in; the two risks are `(*)` for a virtual class and the tower assembly |
| L5b′ | `K₁(C(X)) = 0` for an even-cell finite complex | **lower priority than the refutation**, and now **without a K-theory stack under it**; needed only for the `K₁(A) = 0` clause of printed Theorem 1, which is off the critical path for LIX itself (§B.6, Removal 1) |
| L7 | the five LIX lanes | elementary C\*-algebra; ~4000–6000 lines; no research content. L0's analytic floor is already landed (C8) |

**Where the campaign can still fail (revision 3).** Revision 2 named Bott
periodicity and Leray–Hirsch. **Both are off the critical path** — §B.9 deletes
them. The risks are now:

1. **The Euler wall — now the campaign's single remaining topological wall.**
   `found-euler-class` reports they cannot bridge "the section has exactly one
   transverse zero" to "the top class is nonzero", and they are right that as
   stated it *is* the Thom isomorphism plus localization plus manifold theory.
   It decomposes, and three of the four pieces are cheap here — see §B.10. The
   irreducible piece is **E1**, the relative top class, which is the Thom class
   in disguise. If E1 proves unreachable, the fallback is to state E1 alone as
   the campaign's single named `Prop` — one layer below, and much smaller than,
   the withdrawn `TwistedCancellationFailure`.

   *Two things that bound how far this can be simplified.* The Euler side cannot
   be replaced by structure: Lemma 3 applies to `W_g` too, since it restricts to
   `V` on the slice, so the contradiction **is** Euler-count-versus-parity, and
   the zero count is the only place the hypothesis `g e = s` enters. And the `Y`
   factor does not split off: if `W_g` were an external product `W₁ ⊠ H` then
   `⟨w_{2m}(H),[Y]⟩ = 1` would be a pure cohomology-ring computation and only a
   rank-3 bundle over the 6-manifold `S¹×S⁵` would need an Euler count — but `g`
   is arbitrary and mixes the summands. I looked for such a splitting; it is not
   there.

2. ~~**Wu's formula for a virtual class.**~~ **Resolved** — see §B.9; it is now
   Cartan plus a two-line multiplicativity argument.
2. **The tower assembly, and *which* criterion is proved.** §B.9 closes the
   general stage as far as I can check it on paper — `b_n = 0` for every even
   `n`, via `(j,k) = (n/2-1, n/2+1)`. Until that is Lean-checked at general `ℓ`
   rather than at `Y = pt` and `Y = CP²`, it is a paper argument, and paper
   arguments in this campaign have been wrong before (this section, in revision
   2, was one). §B.9.1 records two inequivalent criteria — `Σd_j` even versus
   every `d_j` even — that agree on the tower and disagree on `CP¹ × CP¹`;
   whichever `lix-obstruction` verifies is the one the doc must carry, and if it
   is the `r-2` route then `⟨v₂·γ_{r-1},[N]⟩ = 0` is a third item to verify.
3. **Steenrod squares themselves.** Cup-`i` products via equivariant acyclic
   carriers, up to Cartan and instability, are now on the critical path where
   revision 2 had them deleted. This is the largest single new build.

*Superseded risk:* Bott periodicity, which had never been formalized in Lean and
was revision 2's highest-risk item, is no longer needed at all.

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
