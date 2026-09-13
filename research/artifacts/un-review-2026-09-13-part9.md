# UN review, part 9: arithmetical position, coarse separation, and K_1 at the paradox extreme

Verifier `un-verify` (UN swarm), 2026-09-13. Subjects: `un-open-6` (`7b9ebd2a6f`), `un-open-7` (`47fd74e1a7`) and
`un-k1-homology` (`5c83d35b84`).

| item | node | verdict |
|---|---|---|
| (6A) | `effective-subshift-invariant-measure-existence-is-pi01` | PASS |
| (6B) | `effective-free-group-kazhdan-lef-type-is-pi01` | PASS |
| (7a) | `un-ladder-rf-rigidity-is-free-mf-rigidity-is-dynamical` | PASS |
| (7b) | `lef-infinite-simple-groups-are-qi-rigid` | PASS (scope note on the consequence paragraph) |
| (k1) | `purely-infinite-steinberg-gl-max-mf-quotient-is-k1` | PASS |
| (k2) | `steinberg-gl-mf-radical-is-commutator-or-trivial` | PASS |
| (k3) | `irreducible-sft-leavitt-gl-max-mf-quotient-formula` | PASS |
| (k4) | `matui-sft-groupoid-homology-is-k-theory` (import) | PASS (verbatim) |

The open nodes of these landings were not reviewed: `effective-free-group-kazhdan-lef-type-is-pi01-complete`,
`elementary-group-lef-growth-separates-subshifts`, `paradox-side-elementary-group-is-finitely-presented` and
`steinberg-gl-max-mf-quotient-is-low-degree-homology`.

## 1. un-open-6

**(6A) The measure test.**
- **Programs.** `Adm(e,n)` excludes translates `g·p` of the first `n` enumerated forbidden patterns with
  `g·supp(p) ⊆ B_n`. `LP(e,n)` imposes, for `s ∈ S` and `w ∈ A^{B_(n−1)}`,
  `Σ_{q|B_(n−1)=w} ρ(q) = Σ_{q|sB_(n−1)=s·w} ρ(q)`, and `sB_(n−1) ⊆ B_n`. The data are finite and rational, so
  feasibility is decidable and `∀n LP(e,n)` is `Π⁰₁`, uniformly in `e`.
- **Measure ⇒ programs.** Take `ρ(q) = μ([q at B_n])`. Inadmissible patterns contain a forbidden translate, so their
  cylinders miss `X_e`.
- **Programs ⇒ measure.**
  - Marginals of marginals agree. A diagonal subsequence makes every `q_(n,m)` converge, and Kolmogorov extension on
    the compact `A^Γ` gives `μ`.
  - For `m ≤ n−1`, summing the level-`n` equation over extensions of `w′ ∈ A^{B_m}` gives
    `μ_n([w′ at B_m]) = μ_n([s·w′ at sB_m])`, and `s·[w′ at B_m] = [s·w′ at sB_m]` because `(g·x)(h) = x(g⁻¹h)`.
  - The equation passes to the limit, generators give all of `Γ`, and forbidden translates get zero mass once
    enumerated and inside the ball.

**(6B) The LEF type on the promise class.**
- **Finite generation:** `u_g χ_Y u_g⁻¹ = χ_{gY}` and `gY = {y : y(g) = a}` for `Y = {x(1) = a}`, so the finitely many
  `χ_{x(1)=a}`, the `u_s^{±1}` and `F_q` generate the ring. EJZ gives (T).
- **Measure side:** it rests on `free-group-crossed-product-matricial-iff-invariant-measure` ((i) ⇒ (ii)) and
  `residually-finite-actions-give-matricial-crossed-products`. Both have PASS lines by un-verify-measure.
- **Paradox side:** it rests on the canonical `no-invariant-measure-steinberg-elementary-no-mf-quotient` (part 3 §3).
  A nontrivial group with no nontrivial MF quotient is not MF, hence not LEF.
- **Both biconditionals** follow on `𝒫`, since LEF implies MF implies a nontrivial MF quotient. `P` is `Π⁰₁` by (6A).
- **Scope:** correctly stated as a promise-class upper bound.

## 2. un-open-7

**(7a) Rigidity against residually finite targets is free.**
- **Perfect:** `e_ij(r) = [e_il(r), e_lj(1)]` for distinct `i, j, l`.
- **Finite quotients:** with `K = ker φ`, either `K ≤ Z` (then `S = G/Z` is a quotient of `G/K`, finite, contradicting
  `S` infinite) or `KZ = G` (then `G/K ≅ Z/(Z∩K)` is abelian, hence trivial).
- **Residually finite targets:** an injective image of `S` is residually finite. A finite quotient separating one
  `s ≠ 1` has trivial kernel by simplicity, so `S` would be finite, a contradiction.
- **The linear corollary** uses Malcev on the finitely generated image. `S` is finitely generated under the stated (T),
  as the node says.

**(7b) Coarse separation.**
- **Items 1–3.**
  - Finite presentation plus LEF gives residual finiteness (Vershik–Gordon, through
    `fp-upgrades-make-non-lef-and-non-lea-cheap`). An infinite simple group is not residually finite by (7a).
  - Finite presentability is a quasi-isometry invariant of finitely generated groups (classical, recalled).
  - The model tests are consistent: V is not LEF, the finitary alternating group is not finitely presented.
- **Scope note (not a defect of items 1–3).** The consequence paragraph applies the theorem to every measure-side rung
  `S = EL_n(R)/Z`. That needs `S` LEF, which the node does not derive in general.
  - It holds when the central scalars map to central scalars of the finite models: the Pestov construction, §3.3.
  - The same argument works for Steinberg rings with centre `k^×` and exact matricial models.
  - Finite generation needs `k` finite.

## 3. un-k1-homology

**(k1) Local compressibility gives `K_1`.**
- **The idempotents:** `a = χ_U` and `b = χ_V` with `a^*a = 1_(s(U)) = 1_A` and `aa^* = 1_(r(U)) ≤ 1_A`. `U⁻¹V` is
  empty because `r(U) ∩ r(V) = ∅`, so `a^*b = 0`. With `1_A a = a` and `1_A b = b`, `x 1_A y = diag(1_A, 1_A)`.
- **Larki:** Theorem 3.4 was checked against the arXiv:1901.07094v2 PDF text: "Let G be a strongly effective, ample and
  Hausdorff groupoid and let K be a field. Suppose that B is a basis of compact open sets for G(0). Then the following
  are equivalent: (1) AK(G) is properly purely infinite. (2) For every V ∈ B, 1V is properly infinite. … (4) Every
  nonzero one-sided ideal in any quotient of AK(G) contains an infinite idempotent."
- **Pure infiniteness:** minimal plus effective gives strongly effective. With simplicity (Steinberg's corollary),
  every nonzero right ideal contains an infinite idempotent and `R` is not a division ring, which is the AGP definition.
- **Classification:** the canonical `K_1` classification (`purely-infinite-canonical-k1-all-ranks`, Lean-backed)
  applies.
- **Calibrations:** for the Cuntz groupoid, `U = {(w1x, 1, wx)}` is a compact open bisection with source `[w]` and range
  `[w1]`. A minimal Z-subshift fails (PI) because `μ(r(U)) + μ(r(V)) = 2μ(A) > μ(A)`.

**(k2) Two extremes.**
- The paradox extreme is (k1).
- The measure extreme is the reviewed `exactly-matricial-rings-have-lef-general-linear-groups`.
- Exclusion: a matricial ring is stably finite, while (PI) at `A = X` gives `a^*a = 1 ≠ aa^*`.

**(k3) Finite graphs.**
- Finite, cofinal, sink-free (L) graphs satisfy Abrams–Aranda Pino (i)–(iii) (import, older node).
- ABC Corollary 7.7 over the PID `k` gives
  `K_1 = Coker(1 − N^t | (k^×)^{E⁰}) ⊕ Ker(1 − N^t | ℤ^{E⁰})`, and right exactness gives the tensor form.
- **Calibrations recomputed:**
  - rose `R_d`: `ℤ/(d−1) ⊗ k^× = k^×/(k^×)^{d−1}`, which is tex Cor l.1297;
  - `N = [[1,1],[1,0]]`: `1 − N^t = [[0,−1],[−1,1]]`, determinant `−1`, so both terms vanish;
  - `N = [[2,1],[1,2]]`: `1 − N^t = [[−1,−1],[−1,−1]]` has Smith form `diag(1,0)`, so `Coker ≅ ℤ` and `Ker ≅ ℤ`.
- The convention remark (transpose invariance of Smith invariants) is correct.

**(k4) Matui import, verbatim** against the arXiv:0909.1624v3 PDF text.
- Setting: "Let σ be a one-sided subshift of finite type on a compact totally disconnected space X. We assume that σ is
  surjective. The étale groupoid G associated with σ is given by G = {(x, n, y) ∈ X × Z × X | ∃k, l ∈ N, n = k−l,
  σ^k(x) = σ^l(y)}."
- "K0(Cr∗(G)) ≅ Coker(id −π) and K1(Cr∗(G)) ≅ Ker(id −π)".
- Theorem 4.14: "When G is the étale groupoid arising from a subshift of finite type, H0(G) ≅ K0(Cr∗(G)),
  H1(G) ≅ K1(Cr∗(G)) and Hn(G) = 0 for all n ≥ 2."
