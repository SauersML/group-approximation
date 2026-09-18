---
rg: 2
id: euler-ring-symbols-in-small-finite-quotients
kind: claim
title: The symbols {π_0, π_q} die in the folding quotients F_(2,l) and F_(r,N) for r <= l - 1; the cyclotomic point u -> ζ_l - 1 detects them on A, but its σ-orbit does not
distinct_from:
  euler-ring-rational-symbols-are-infinitely-generated: that proves the c_q independent in K_2(D); this asks which finite quotients of D still see them.
  euler-ring-steinberg-rf-residual-is-fng: that is the open question whether the finite residual of St_N(D) is finitely normally generated; this computes the smallest test cases for it and does not decide it.
artifacts:
  - research/artifacts/gq-gq-k2-q-rf-hosts.md
  - research/artifacts/gq-referee-a-euler-ring-symbols-in-small-finite-quotients.md
  - research/artifacts/gq-referee-b-euler-ring-symbols-in-small-finite-quotients.md
---

**ESTABLISHED (2026-09-18)** through `euler-ring-symbols-in-small-finite-quotients-proof`. Lane proof (gq-k2-q). *Reviewed:* PASS by
`gq-referee-a` (`research/artifacts/gq-referee-a-euler-ring-symbols-in-small-finite-quotients.md`); nits N1–N5 are applied. Citation review PASS by
`gq-referee-b` (`research/artifacts/gq-referee-b-euler-ring-symbols-in-small-finite-quotients.md`). Inputs:
- the identities (S1)–(S4) and Stein's generation theorem for radical ideals, and the order of `K_2(O/P^m)`, from the
  Dennis–Stein survey, LNM 342, pp. 249, 252 and 254, read at the source;
- textbook facts, not re-read: Morita invariance of `K_2`, the Artin–Hasse formula, and the two level bounds for
  the `l`-th Hilbert symbol of `Q_l(ζ_l)`.

## Setting

- `A`, `σ`, `D` and `π_k = u + 1 + kl` are as in `euler-ring-rational-symbols-are-infinitely-generated`.
- `c_q = {π_0, π_q}` for primes `q != l`.
- `F_(2,l) = C ⋊ <X>`, with `C = Z/l^2[y]/(y^2, ly)`, `X y X^(-1) = y + l`, `X^l = 1`. `D -> F_(2,l)` sends `u` to
  `y` and `x` to `X`. This is the test ring of `euler-ring-steinberg-rf-residual-is-fng`, Attempt 1.

## Statement

1. **The two-step quotient kills every c_q.** For every prime `l`, every prime `q != l` and every `N >= 3`, the
   image of `c_q` in `K_2(N, C)` is trivial, and so is its image in `K_2(N, F_(2,l))`.
   - More generally, for `l` odd and `1 <= r <= l − 1`, the image `C_r` of `A` in `F_(r,N)` is `Z[u]/(l,u)^r`, and
     `K_2(N, C_r) = 0`. So every `c_q` dies in every `F_(r,N)` with `r <= l − 1`.
2. **The cyclotomic point detects c_q on A.** Let `l` be odd, `K = Q_l(ζ)` with `ζ` a primitive `l`-th root of unity,
   `𝔭 = (ζ − 1)`, and `n >= l + 1`.
   - Then `u -> ζ − 1` defines a ring map `A -> O_K/𝔭^n`, and the image of `c_q` in `K_2(O_K/𝔭^n)` has `l`-th
     Hilbert symbol `ζ^(-q)`, up to the sign convention of the Artin–Hasse formula.
   - This is nontrivial for every `q != l`. So the detection `q -> q mod l` exists on commutative quotients of `A`.
3. **Its σ-orbit is blind.** Let `m >= 1` with `ml ∈ 𝔭^n`. The orbit `ζ − 1 + il` (`i ∈ Z/m`) gives a ring map
   `ρ_m : D -> M_m(O_K/𝔭^n)`.
   - `K_2(M_m(O_K/𝔭^n)) ≅ K_2(O_K/𝔭^n) ≅ Z/l`, detected by the Hilbert symbol. The image of `c_q` there has
     Hilbert symbol `ζ^(-qm)`.
   - So the image is trivial, because `ml ∈ 𝔭^n` with `n >= l + 1` forces `l | m`.
   - The image of `c_q` in `K_2` of the commutative ring `ρ_m(A)` is nontrivial, by item 2.

## What is not claimed

- The folding quotients `F_(r,N)` with `r >= max(l, 3)` are not treated. At `r = l` the
  argument breaks, and the expected survivor of `K_2(C_l)` is the class of `u^(l−1) du`.
- Whether `c_q` vanishes in `K_2(ρ_m(D))`, the crossed product itself, is not decided. Items 2 and 3 locate the
  question there: the commutative part sees `c_q`, and the ambient matrix ring does not.
- `euler-ring-steinberg-rf-residual-is-fng` stays OPEN.

## Consequences

- **The heuristic detection map.** On `A`, finite quotients do see `c_q` through `q mod l`, as one would hope for a
  detection through `q -> q` in `Z_l^x`. But the orbit sum multiplies the value by the orbit length, which is
  divisible by `l`.
  - In `F_(2,l)` the mechanism is different. There `c_q = z^q` for the single class `z = {1+y, 1+l}` (`l` odd), and
    a Steinberg relation kills `z`.
- **The ambient detector of the folding quotients is blind.** For `l` odd, `F_(r,N)` acts on the free
  `Z/l^r`-module `M_(r,N)`. So it lies in `M_N(Z/l^r)`, where `K_2 = K_2(Z/l^r) = 0` (Dennis–Stein, p. 255).
  - A detection of `c_q` in `F_(r,N)` therefore has to be intrinsic to `K_2(F_(r,N))`.
  - The same holds for any map to a matrix ring over a ring with `K_2 = 0`. Item 3 shows that a matrix ring with
    `K_2 != 0` does not help along a single orbit.
