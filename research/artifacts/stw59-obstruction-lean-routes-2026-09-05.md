# Lean routes to the STW LIX parity obstruction (manuscript §2)

Lane `lix-obstruction`, 5 September 2026. Scope: manuscript
`stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md` §2, i.e. Lemma 2
(twisted cancellation failure) and Lemma 3 (mapping-torus parity). Everything
below is about how to get those two into Lean unconditionally.

**Verdict, cheapest first.** The printed route (complex K-theory, Bott
periodicity, the Chern character with its integral normalization, the
Künneth isomorphism, the splitting principle) is *not* the cheapest route.
Lemma 3 admits a purely **mod 2** proof by Wu's formula, verified by hand here
for `Y = pt` and `Y = CP²`. That deletes K-theory, Bott periodicity, the Chern
character and integral Künneth from the ingredient list, replacing them with
Steenrod's `Sq²` and `Sq⁴` and two instances of the Wu relation for mod-2 Chern
classes. It also downgrades the Euler-class requirement from a signed, oriented
count to a mod-2 count, and it lands on top of a mod-2 cohomology apparatus that
**already exists, sorry-free, in this repository**.

---

## 0. What is actually irreducible

Before comparing routes it is worth pinning what no route can dodge.

A counterexample to K₁-injectivity is a unital algebra `B` with `u ∈ U(B)`,
`u ∉ U₀(B)`, `[u] = 0 ∈ K₁(B)`. For a homogeneous block `B = Γ(X, End E)` with
`rank E = n`, `U(B)/U₀(B) = [X, U(n)]` and `K₁(B) = K¹(X)`, and the kernel of
`[X,U(n)] → [X,U(n+1)]` is the image of `[ΣX, S^{2n+1}] = H^{2n}(X;ℤ)`. So
non-injectivity requires `dim X ≥ 2n` and is driven by `π_{2n}(U(n)) ≅ ℤ/n!`.
The minimal case is `n = 2`: `π₄(U(2)) ≅ π₄(SU(2)) = π₄(S³) = ℤ/2`.

Consequently:

* Lemma 2 at `Y = pt` says `F ≇ 1²` over `S⁵`, which is exactly
  `π₄(S³) ≠ 0`. **Any** Lean proof of Lemma 2 proves `π₄(S³) ≠ 0`.
* Every known unital simple non-K₁-injective algebra is Villadsen-type and
  routes through `π_{2n}(U(n)) ≠ 0`; Rieffel's theorem (stable rank one ⇒
  `U/U₀ ≅ K₁`) forces any counterexample out of the stable-rank-one world, and
  no alternative mechanism is known. There is no cheaper counterexample to
  look for.

Calibration: `π₄(S³) = ℤ/2` has been formalized once, in cubical Agda's
synthetic homotopy theory (the Brunerie number). It does not transfer to
Mathlib's `TopologicalSpace`. So the question is not "is there something easy
here" — there is not — but "what is the smallest classical apparatus that
produces it". Answer: two Wu relations.

---

## 1. The repo's own odd-degree engine — what it really gives

`GroupApproximation/ThirdParty/HamSandwich/SphereOddDegree/` (199 files,
sorry-free, namespace-isolated, being brought green on v4.32 by
`hamsandwich-port-A/B`). Read for generality, not for the `RP^n` headline.

**General over arbitrary spaces (this is the important part):**

| file | gives |
|---|---|
| `AlgebraicTopology/SingularCohomology.lean` | `singularCohomologyFunctor R M : TopCatᵒᵖ ⥤ ...`, contravariant, functorial. Any commutative ring, any coefficient module. |
| `AlgebraicTopology/CupProduct.lean` | cochain-level Alexander–Whitney cup, bilinear, natural, unital, with degree-`n` powers. |
| `AlgebraicTopology/CochainCupLeibniz.lean` + `CohomologyCupProduct.lean` | the **descent to cohomology**: `cupZMod2 : H^p(X;F₂) → H^q(X;F₂) → H^{p+q}(X;F₂)`, well defined, for arbitrary `X`. |
| `AlgebraicTopology/MayerVietoris.lean` | MV long exact sequence and connecting iso for an arbitrary open cover `U ⊔ V = ⊤` of an arbitrary space. |
| `AlgebraicTopology/{BarycentricSubdivision*,SmallChains*,IteratedSubdivision*}` | subdivision, Lebesgue number, small-chains quasi-iso — the excision engine, fully general. |
| `AlgebraicTopology/{HomotopyInvariance,SingularHomologyHomotopyInvariance,SingularCohomologyHomotopyInvariance}.lean` | homotopy invariance, now unconditional against Mathlib v4.32's prism operator. |
| `SphereTopHomology.lean`, `AlgebraicTopology/Degree.lean` | `Hₙ(Sⁿ;ℤ) ≅ ℤ`, integral degree with `degree_id`, `degree_comp`, homotopy invariance, choice-independence. |
| `BorsukUlam.lean` | `no_odd_map_sphere_succ`, `borsuk_ulam`. |

**Specific to `RP^n` and spheres:** the mod-2 cohomology *ring* of `RP^n`
(`RPnCellularDiagonal`, `RPnCupProduct*`, ~40 files), the double cover, its
transfer, the Gysin connecting map, `ModTwoDegreeComparison`.

**Answer to the question asked.** Over spaces other than `RP^n` and spheres the
development gives a genuine, general **mod-2 singular cohomology ring functor
with Mayer–Vietoris and homotopy invariance**. That is materially more than
"an `RP^n` gadget": it is exactly the base one needs to compute
`H^*(CP^d;F₂)`, `H^*(S¹×S⁵×Y;F₂)` and their ring structures by MV induction over
the even-cell filtration. What it does **not** contain: Steenrod squares,
characteristic classes of any kind, vector bundles, K-theory, Künneth (in any
form), Poincaré duality, Thom classes.

Note for the port lanes: the header docstring of `CupProduct.lean` still says
the cohomology-level descent is "the exact remaining blocker". That is stale —
`CohomologyCupProduct.lean` performs the descent. Worth fixing so nobody
re-derives it.

**Can the parity be detected mod 2? Yes.** See §2. And yes, `Y` may be replaced
by a cheaper base for the *first* stage — but see the correction in §6: the
tower needs the obstruction at every stage, so `Y = CP²` alone is a milestone,
not the target.

---

## 2. The recommended route: Lemma 3 by Wu's formula, mod 2

Write `γ_i(E) = c_i(E) mod 2 ∈ H^{2i}(-;F₂)`. For a complex bundle these are the
even Stiefel–Whitney classes of the underlying real bundle (`w_{2i} = γ_i`,
`w_odd = 0`). The Wu formula for mod-2 Chern classes,

```
Sq^{2i}(c_j) = Σ_{t=0}^{i} binom(j+t-i-1, t) · c_{i-t} · c_{j+t}   (mod 2),
```

is a splitting-principle computation: on a sum of lines, `γ = ∏(1+y_k)` with
`|y_k| = 2` and `Sq(y_k) = y_k + y_k²` (the odd squares vanish because `y_k` is
the reduction of an integral class), so `Sq(γ) = ∏(1 + y_k + y_k²)`; extracting
components gives the displayed relation. Only two instances are needed:

```
(W2)   Sq²(c₂) = c₁c₂ + c₃
(W4)   Sq⁴(c₃) = c₂c₃ + c₁c₄ + c₅
```

### 2.1 `Y = pt` (this is Bott's `(n-1)!` at `n = 3`, in three lines)

`N = S¹ × S⁵`, `V = 1³`, `r = 3`, `dim N = 6 = 2r`.
`H²(N;F₂) = H⁴(N;F₂) = 0`, so `γ₁ = γ₂ = 0`, and (W2) gives

```
γ₃(W) = Sq²(γ₂(W)) + γ₁(W)γ₂(W) = 0.
```

`γ₃(W) = c₃(W) mod 2`, so `⟨c₃(W), [S¹×S⁵]⟩ ∈ 2ℤ`. That is Lemma 3 for `Y = pt`,
i.e. the statement that a rank-3 bundle on `S¹×S⁵` restricting to a trivial
bundle on a slice has even top Chern number. The printed proof of this reaches
for the Chern character and the integral normalization of the Bott generator on
`S⁶`; mod 2 it is two vanishing cohomology groups.

### 2.2 `Y = CP²` (`r = 5`, `dim N = 10`)

`H^*(N;F₂) = Λ(t,x) ⊗ F₂[h]/(h³)`, `|t| = 1`, `|x| = 5`, `|h| = 2`.
Every even class decomposes as `a + t x b` with `a, b ∈ H^{even}(Y;F₂)`,
because `t·even` and `x·even` are odd.

Restricting to the slice `{1}×M` kills `t`, so `a = γ(V) = (1+h)² = 1 + h²`.
Hence

```
γ₁(W) = 0,   γ₂(W) = h²,   γ₃(W) = t x b₀,   γ₄(W) = t x b₁ h,   γ₅(W) = t x b₂ h².
```

* `γ₁(W) = 0`: `H²(N;F₂) → H²(M;F₂)` is an isomorphism and `c₁(V) = 2h ≡ 0`.
* `γ₃(W) = 0`: it is `t x b₀`, and `H⁶(N;F₂) → H⁶(S¹×S⁵×{y};F₂)` sends
  `tx ↦ tx ≠ 0`; the restricted bundle is covered by §2.1, so `b₀ = 0`.
* (W4) with `γ₃ = 0` and `γ₁ = 0`:
  `γ₅(W) = Sq⁴(γ₃) + γ₂γ₃ + γ₁γ₄ = 0`.

So `w_top(W) = 0` for **every** rank-5 complex `W` on `S¹×S⁵×CP²` restricting to
`V` on a slice. Lemma 3 at the first nontrivial stage, with no K-theory.

### 2.3 The mod-2 side of Lemma 2

The contradiction only needs an **odd** zero count, so the whole signed/oriented
apparatus goes away:

* `w_top` of a rank-`r` complex bundle on a closed `2r`-manifold is the
  obstruction to a nowhere-zero section, and a section with a single
  nondegenerate zero forces `w_top ≠ 0` (the local class generates
  `H^{2r}(N, N∖z;F₂) ≅ H^{2r}(N;F₂) ≅ F₂`).
* `⟨c_m(H),[Y]⟩ = ±1` is not needed at all. In the rank-one-projection model of
  `CP^d`, `H = L^{⊕d}` has the explicit section
  `σ(q) = (q a₁, …, q a_d)` with `a₁,…,a_d` the first `d` standard basis
  vectors of `ℂ^{d+1}`. Its zero set is `{q : q a₁ = … = q a_d = 0}` = the
  single point `q = e_{d+1} e_{d+1}ᴴ` (the line orthogonal to
  `span(a₁,…,a_d)`), and the zero is nondegenerate — in the affine chart
  `v = (z₁,…,z_d,1)` the section reads `(z̄₁,…,z̄_d)` up to a positive scalar,
  a real-linear isomorphism. For a product `Y = ∏CP^{d_j}` take the product of
  these: still exactly one zero.
* The section `S(x,y,t) = ((1-t)e₃ + t x, χ(t)σ(y))` of (2.10) has zero set
  `{t = 1/2, x = -e₃, σ(y) = 0}` — one point — and the derivative of its
  `ℂ³`-component there is `(ξ,a) ↦ ξ/2 − 2a e₃` on
  `T_{-e₃}S⁵ ⊕ ℝ → ℂ³`, a real-linear isomorphism (if `ξ/2 = 2a e₃` with
  `Re⟨ξ,e₃⟩ = 0` and `a` real then `ξ = 4a e₃` forces `a = 0`).

### 2.4 What the mod-2 route costs

| ingredient | status |
|---|---|
| general singular `F₂` cohomology, cup product, MV, homotopy invariance | **in the repo**, sorry-free |
| `H^*(CP^d;F₂)`, `H^*(S¹×S⁵×∏CP^{d_j};F₂)` as rings | MV induction on the even-cell filtration; `F₂` is a field so Künneth has **no Tor term** — this is field-coefficient Künneth, not the integral torsion-free Künneth |
| complex bundles as projection-valued maps, `⊕`, pullback, homotopy invariance | `found-bundle-calculus` (already scoped) |
| mod-2 Chern classes `γ_i`, Whitney sum, splitting principle | needed; *mod 2 only* |
| `Sq²`, `Sq⁴`: cochain `∪₁`, `∪₂` and their coboundary formulas | **the one genuinely new foundation** |
| Wu relations (W2), (W4) | symmetric-function extraction from `Sq(γ) = ∏(1+y+y²)` |
| mod-2 Euler class = `w_top`, single nondegenerate zero ⇒ `w_top ≠ 0` | needed; no orientation, no signs, no signed index |

What this **deletes** relative to the printed route: `K⁰`/`K¹`, the split
restriction sequence, K-theory Künneth, Bott periodicity, the Chern character
and its integral normalization on `S¹` and `S⁵`, the identity
`c_q(δ) = (−1)^{q−1}(q−1)! ch_q(δ)`, the evenness of `(|b|+2)!/∏b_j!`, integral
torsion-freeness of `H^*(S¹×S⁵×Y)`, integral Chern classes, and the oriented
Euler number with signed local indices.

---

## 3. Route 2 — a finite chain-level certificate. **Rejected.**

Asked: is there a finite CW/simplicial model in which the class of `u`, or the
parity of Lemma 3, becomes a finite integer computation?

No, and the reason is structural rather than a matter of size. The parity is
`π₄(S³) = ℤ/2` in disguise. Computing it combinatorially means the Whitehead
tower: `π₄(S³) = H₄(S³⟨3⟩)` where `S³⟨3⟩` is the fibre of `S³ → K(ℤ,3)`. A
simplicial model of that fibre is a twisted cartesian product with `K(ℤ,2)`,
whose simplicial sets have **infinitely many simplices in every positive
degree**; Kenzo computes with it only through effective-homology reductions
(the basic perturbation lemma), not through a finite complex. There is no
finite simplicial model of `S³⟨3⟩` to enumerate: it is 3-connected with
`H₄ = ℤ/2` and nontrivial homology in unboundedly many degrees.

Direct obstruction-theoretic certificates are circular: the obstruction to a
nullhomotopy of `u` lives in `H^*(X; π_*(U(2)))`, and the coefficient group is
the thing being computed.

Concrete sizes, since they were asked for: the cheapest honest chain-level
statement is not "a model with `N` cells" but "a formalization of effective
homology + the basic perturbation lemma + a twisted Eilenberg–Zilber theorem",
which no proof assistant has for this computation. A `10⁶`-cell model would be
a bargain; none exists at any size.

## 4. Route 3 — narrow Euler-class theory. **Necessary, not sufficient.**

The requested statement — a continuous section of a rank-`r` complex bundle
over a closed oriented `2r`-manifold with isolated transverse zeros has a
signed zero count independent of the section — is one half of Lemma 2 and
supplies **nothing** toward Lemma 3. Independence of the section says the count
is an invariant of `W_g`; the contradiction still needs an independent proof
that the invariant is even, which is exactly Lemma 3.

Cost of the integral version, honestly: it needs oriented local degree at a
zero, a tubular-neighbourhood or Thom-class argument, and the comparison of two
sections through a homotopy with a 1-parameter zero set — i.e. transversality in
families. Mathlib has no manifold degree theory and no Thom class. Order of
magnitude: comparable to the whole 199-file `SphereOddDegree` development, for
half of one lemma.

The **mod-2** version (§2.3) is much cheaper — no orientations, no signed
indices, no oriented local degree — and it is what the recommended route needs.
Recommendation to `found-euler-class`: build the mod-2 version first, and do not
build the `⟨c_m(H),[Y]⟩ = ±1` pairing at all (the explicit single-zero section
replaces it).

## 5. Route 4 — a ℤ/2 invariant of the clutching function `u : S⁴ → U(2)`.
**Rejected in the form proposed; the mod-2 route of §2 is its viable cousin.**

The suggestion was a mod-2 linking/degree invariant computed from `SU(2) = S³`,
using the vendored degree theory. The invariant that detects `π₄(S³) = ℤ/2` is
the Pontryagin one: take a regular value of `f : S⁴ → S³`, get a framed
1-manifold in `S⁴`, and read the framing class in `π₁(SO(3)) = ℤ/2`. Making
that a Lean invariant means transversality, framed cobordism, and the
Pontryagin–Thom correspondence — strictly more than route 3, and the vendored
degree theory does not touch it (it computes `[Sⁿ,Sⁿ]`, and the obstruction is
in `[S⁴,S³]`, where degree is identically undefined).

The cohomological cousin — Steenrod's `Sq²` on the mapping cone: `Sq²` is an
isomorphism `H³(C_f) → H⁵(C_f)` iff `f` generates `π₄(S³)` — is real, but it
needs an *explicit* representative of `Ση`, the identification `ΣCP² = C_{Ση}`,
`H^*(CP²;F₂)` with its ring structure, `Sq²x = x²`, and stability of `Sq²` under
suspension; and even then it delivers only `Y = pt`, i.e. `F ≇ 1²` on `S⁵`. It
does **not** give the twisted Lemma 2. The §2 route uses the same `Sq` machinery
and delivers the twisted statement, so it strictly dominates.

---

## 6. Two corrections to the brief

**(a) `Y = CP²` alone does not refute LIX.** §4's tower needs Corollary 4 at
every stage `i`, with `Y_i = ∏_{j<i} CP^{r_j}` growing, and the doubling
`r_{i+1} = 2r_i` is forced. Reason: a unital `*`-homomorphism
`C(X_i) ⊗ M_{r_i} → Γ(X_{i+1}, End E_{i+1})` has the normal form
`a ↦ ⊕_k (a ∘ λ_k) ⊗ 1_{V_k}`, so a point-evaluation summand
(`λ_k ≡ x_i`, needed for simplicity) contributes `E_i(x_i) ⊗ V_k`, i.e.
`V_k^{⊕ r_i}`. Taking `V_k` a line gives multiplicity `r_i`, and matching
multiplicity to complex dimension (so that the top mod-2 Chern class of the new
`H` is the top class of the new factor) forces `d_{i+1} = r_i`, hence
`r_{i+1} = r_i + r_i`. No smaller multiplicity is available. So `Y = CP²` closes
Corollary 4 at stage 1 only.

**(b) The general stage is not yet closed mod 2.** Set `γ(W) = a + t x b`, with
`a` fixed by the slice restriction. For the tower, `d_j = 2^j` is even, so
`a = ∏_j (1 + h_j^{d_j})` — very sparse. The natural induction shows the
`tx`-component `b` vanishes degree by degree: to kill `b` in degree `2k` one
needs some `i ≥ 1` with `binom(k+2−i, i)` odd, so that the Wu relation
`Sq^{2i}(γ_{k+3−i}) = … + binom(k+2−i,i) γ_{k+3}` isolates `γ_{k+3}` while all
other terms are pulled back by the inductive hypothesis. That binomial fails to
be odd for some `k` — the first failure is `k = 1`, which is precisely the
`γ₄` gap encountered in §2.2 and routed around there by using (W4) rather than
(W2). Supplementary identities exist (the total relation
`Sq(γ)·γ = ∏(1 + y_k³)`, which does kill the `k = 1` gap for `CP²`). This is a
finite combinatorial question about which Wu relations suffice, not an
obstruction in principle, but **it is open as of this writing** and is the
first thing to settle before the mod-2 route is committed to for the whole
tower.

---

## 7. Recommended Lean lemma chain

Elementary layer (buildable now, no new foundations — this lane):

1. `stw59_taut_complement_add_one` — over `S⁵ ⊂ ℂ³`, `1 - x xᴴ` is a
   projection, `x xᴴ ~ e₁e₁ᴴ` via the partial isometry `x e₁ᴴ`, hence
   `F ⊕ 1 ≅ 1³`.
2. `stw59_section_S_zero_iff` — for `x` in the unit sphere of `ℂ³` and
   `t ∈ [0,1]`, `(1-t) e₃ + t x = 0 ↔ t = 1/2 ∧ x = -e₃`.
3. `stw59_transverse_at_neg_e3` — `(ξ,a) ↦ ξ/2 - 2a e₃` is a real-linear
   isomorphism `{ξ : Re⟨ξ,e₃⟩ = 0} × ℝ ≃ ℂ³`.
4. `stw59_sigma_zero_iff` — in the rank-one-projection model of `CP^d`, the
   section `q ↦ (q a₁,…,q a_d)` of `L^{⊕d}` vanishes exactly at
   `q = e_{d+1}e_{d+1}ᴴ`.
5. `stw59_unitary_of_mvn_complements` — if `p, q ≤ P` are projections with
   `p ~ q` and `P - p ~ P - q` in a C*-algebra, the sum of the two partial
   isometries is a unitary `g` of `P A P` with `g p g* = q`; applied to
   `p = e eᴴ`, `q = s sᴴ` it gives the manuscript's `g` with `g e = s`
   directly, and replaces the polar-decomposition step (Murray–von Neumann
   equivalence is already the unitary notion).

Foundation layer (the seven Opus lanes), in dependency order:

6. mod-2 cohomology rings: `H^*(CP^d;F₂)`, then `H^*(S¹×S⁵×∏CP^{d_j};F₂)`,
   by MV induction over the even-cell filtration, on top of the existing
   `cupZMod2` and `MayerVietoris`. Field-coefficient Künneth.
7. `Sq^i` from cochain `∪_i` products, with naturality and the Cartan formula.
8. mod-2 Chern classes `γ_i` for projection bundles: Whitney sum, splitting
   principle, `Sq(y) = y + y²` on `|y| = 2` integral reductions.
9. (W2), (W4) by extraction from `Sq(γ) = ∏(1+y+y²)`.
10. `stw59_lemma3_pt`, then `stw59_lemma3_CP2` — §2.1, §2.2.
11. mod-2 Euler class: `w_top` as the obstruction to a nowhere-zero section;
    single nondegenerate zero ⇒ `w_top ≠ 0`.
12. `stw59_lemma2_CP2` — combine 1–5, 10, 11.
13. the general-stage induction of §6(b), then `stw59_lemma2`.

Items 1–5 are this lane's immediate work and are independent of every
foundation above.
