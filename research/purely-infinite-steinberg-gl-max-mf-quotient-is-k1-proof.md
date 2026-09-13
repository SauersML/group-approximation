---
rg: 2
id: purely-infinite-steinberg-gl-max-mf-quotient-is-k1-proof
kind: route
title: Local compressibility makes every unit idempotent properly infinite, Larki then gives a purely infinite simple Steinberg algebra, and the canonical K_1 classification applies
target: purely-infinite-steinberg-gl-max-mf-quotient-is-k1
requires:
  - steinberg-algebra-simple-iff-minimal-effective
  - purely-infinite-steinberg-algebras-characterized
  - purely-infinite-canonical-k1-all-ranks
artifacts:
  - research/artifacts/un-k1-homology-2026-09-13-part1.md
---

Notation as in the target. For a compact open bisection `W` write `χ_W ∈ A_k(𝒢)`. Convolution of
characteristic functions of compact open bisections is `χ_W χ_(W') = χ_(W W')`, and `χ_W^* := χ_(W^(-1))`.
So `χ_W^* χ_W = 1_(s(W))` and `χ_W χ_W^* = 1_(r(W))`.

**Step 1: `R` is countable and unital.** `X` is compact open, so `1_X` is the unit. `𝒢` is second
countable and ample, so it has a countable basis of compact open bisections. Every compact open bisection
is a finite union of basic ones, and `A_k(𝒢)` is spanned over `k` by the `χ_W`, `W` basic. `k` is countable.

**Step 2: `R` is simple.** `𝒢` is Hausdorff, ample, effective and minimal; apply
`steinberg-algebra-simple-iff-minimal-effective`.

**Step 3: every `1_A` is properly infinite.** Let `A ⊆ X` be nonempty compact open, and take `U, V` as
in (PI). Put `a = χ_U`, `b = χ_V`. Then:
- `a^* a = 1_A = b^* b`;
- `a a^* = 1_(r(U))` and `b b^* = 1_(r(V))`, both idempotents below `1_A` since `r(U), r(V) ⊆ A`;
- `a^* b = χ_(U^(-1) V) = 0`, because `U^(-1) V ≠ ∅` would need `r(U) ∩ r(V) ≠ ∅`.

So `1_(r(U))` and `1_(r(V))` are orthogonal idempotents below `1_A`, each Murray–von Neumann equivalent to
`1_A` (through `a, a^*` and `b, b^*`). That is proper infiniteness of `1_A`. In Larki's matrix form
(`a ⊕ a ≾ a`, with `a ≾ b` iff `a = x b y`, arXiv:1901.07094 TeX l.191 and l.215): take the column
`x = (a^*, b^*)^t` and the row `y = (a, b)`. Since `1_A a = a` and `1_A b = b`, we get
`x 1_A y = [[a^* a, a^* b],[b^* a, b^* b]] = diag(1_A, 1_A)`.

**Step 4: `R` is purely infinite simple.** `𝒢` is strongly effective in Larki's sense: every nonempty
closed invariant subset of `X` is `X` by minimality, and `𝒢_X = 𝒢` is effective. Take for `𝓑` the basis of
all nonempty compact open subsets of `X`. By Step 3, condition (2) of Larki Thm `thm3.4`
(`purely-infinite-steinberg-algebras-characterized`) holds. So condition (4) holds: every nonzero one-sided
ideal of every quotient of `R` contains an infinite idempotent. With Step 2, every nonzero right ideal of
the simple ring `R` contains an infinite idempotent, and `R` is not a division ring. That is a purely infinite
simple ring in the sense of Ara–Goodearl–Pardo.

**Step 5: classification.** By Steps 1 and 4, `R` is a countable unital purely infinite simple ring. So
`purely-infinite-canonical-k1-all-ranks` gives, for every `n >= 1`: `κ_n` surjective,
`ker κ_n = [GL_n(R), GL_n(R)] = Rad_MF(GL_n(R))`, `K_1(R)` MF, unique factorization of every homomorphism to
an MF group through `κ_n`, and the same for `R^×`.

**Calibration (Cuntz groupoid).** For the full shift on `d` letters, with groupoid elements `(x, n, y)`,
take `A` a cylinder `[w]` and `U = {(w1x, 1, wx) : x}`, `V = {(w2x, 1, wx) : x}`. These are compact open
bisections with `s = [w]`, ranges `[w1]` and `[w2]`, which are disjoint and inside `[w]`. A general compact open
`A` is a finite disjoint union of cylinders, so the piecewise unions satisfy (PI). Then `R = L_k(1,d)`
(`leavitt-path-algebras-are-steinberg-algebras`), and the conclusion is `non_mf_groups_exist.tex` Cor l.1297.
