---
rg: 2
id: rsg-proper-power-germ-torsion-via-cyclic-germ-groups
kind: route
title: Groups of germs at rational points of a finite-nucleus RSG are virtually infinite cyclic, and in such a group an infinite-order element is never conjugate from one power to a power of different absolute value
target: rsg-proper-power-conjugate-germs-torsion-at-finite-orbits
requires: []
artifacts:
  - research/artifacts/bh-bg-rsg-nonisometric-hosts-2026-09-13.md
---

**Item 1 (import).** J. Belk, C. Bleak, F. Matucci, M. C. B. Zaremsky, *Hyperbolic
groups satisfy the Boone--Higman conjecture*, arXiv:2309.06224v3. The source file
`hyperbolic_boone_higman.tex` was read on MSI on 2026-09-13.
- **`prop:CyclicStabilizers`, verbatim:** "Let $G\leq \R_{\Gamma,E}$ be an RSG with
  a finite nucleus, and let $\omega\in E$ be a rational point. Then the group of
  germs\/ $[G]_\omega$ is virtually infinite cyclic."
- **Definition, verbatim from the same page:** "$[G]_x \coloneqq
  \mathrm{Stab}_G(x)\bigr/\mathrm{Fix}_G^0(x)$". Here `Fix^0_G(x)` consists of "all
  elements that are the identity in some neighborhood of~$x$".
- **The paper's own condition.** The proof picks `f` taking `C_σ` to `C_(σ·τ)` by
  the canonical similarity, for `ω = σ·τ^∞`. It then shows that `<[f]_ω>` has
  finite index. That proof uses only that `G` is an RSG and that the nucleus is
  finite, which are the hypotheses of the target.

**Item 2 (iterating the relation).**
- By induction, `f^n g^(k^n) f^-n = g^(l^n)` for `n ≥ 1`. The step is
  `f^(n+1) g^(k^(n+1)) f^-(n+1) = f^n (f g^k f^-1)^(k^n) f^-n = f^n g^(l k^n) f^-n = (f^n g^(k^n) f^-n)^l`.
- Raising to the power `p` gives `f^n (g^p)^(k^n) f^-n = (g^p)^(l^n)`.
- Let `N ≥ 1` be the length of the `f`-orbit of `z`. Then `f^N` and `g^p` both lie
  in `Stab_G(z)`. The germ map `Stab_G(z) → [G]_z` is a homomorphism, so with
  `x = [g^p]_z` and `y = [f^N]_z`:

  `y x^(k^N) y^-1 = x^(l^N)`.

**Item 3 (virtually infinite cyclic groups).** Let `Λ` be virtually infinite
cyclic, and let `x, y ∈ Λ` with `x` of infinite order and `y x^A y^-1 = x^B`,
where `A, B ≠ 0`. Then `|A| = |B|`.
- **An infinite cyclic normal subgroup.**
  - Let `C ≤ Λ` be infinite cyclic of finite index.
  - Its normal core `C_0` is an intersection of finitely many conjugates of `C`.
    So `C_0` has finite index and is normal.
  - `C_0 ≤ C` is nontrivial because `Λ` is infinite. So `C_0 = <c_0>` is infinite
    cyclic.
- **Conjugation acts by a sign.** `y c_0 y^-1` generates `C_0`, so it equals
  `c_0^ε` with `ε = ±1`.
- **Power in the core.** `Λ/C_0` is finite, so `x^m ∈ C_0` for some `m ≥ 1`.
  Write `x^m = c_0^r`. Then `r ≠ 0`, since `x` has infinite order.
- **Comparing exponents.**
  - One side is `y x^(Am) y^-1 = y c_0^(Ar) y^-1 = c_0^(εAr)`.
  - The other side is `x^(Bm) = c_0^(Br)`.
  - So `εAr = Br`, and `|A| = |B|`.

**Item 4 (conclusion).**
- By Item 1, `[G]_z` is virtually infinite cyclic, since `z` is rational.
- Suppose `x = [g^p]_z` has infinite order. Items 2 and 3 with `A = k^N` and
  `B = l^N` give `|k|^N = |l|^N`, so `|k| = |l|`. This contradicts the hypothesis.
- So `x` has finite order `m`. Then `g^(pm) ∈ Fix^0_G(z)`, so `g^(pm)` is the
  identity on a neighbourhood of `z`.

**Consequences in the target.**
- **`BG`.** Put `f = b` and `g = a`, with `k = 1` and `l = 2`.
- **`H4`.** Put `f = g_i` and `g = g_(i+1)`, with `k = 1` and `l = 2`.
- Images of relations in a homomorphism are relations, so the images satisfy the
  hypothesis whether or not the homomorphism is injective.
