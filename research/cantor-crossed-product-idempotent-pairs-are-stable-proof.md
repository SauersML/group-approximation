---
rg: 2
id: cantor-crossed-product-idempotent-pairs-are-stable-proof
kind: route
title: The right inverse of (1−e)a gives an idempotent equivalent to 1−e, internal cancellation supplies the complement, and Ehrlich's completion gives unit-regularity
target: cantor-crossed-product-idempotent-pairs-are-stable
requires: [minimal-cantor-crossed-products-have-internal-cancellation]
artifacts:
  - research/artifacts/sk-algebraic-putnam-2026-09-13-part2.md
---

Here `p ~ q` for idempotents means `pR ≅ qR`, i.e. `x ∈ pRq`, `y ∈ qRp` with `xy = p`, `yx = q`. Parts 1 and 2 use only ring identities plus internal cancellation. Part 3 is an import.

**1. Idempotent pairs.**
- Let `ar + es = 1` and `α = (1−e)a`. Then `αr = (1−e)ar = 1−e`, since `(1−e)es = 0`.
- `π := rα` satisfies `π² = r(αr)α = r(1−e)α = rα = π`, since `(1−e)α = α`. Also `απ = α`.
- `π ~ 1−e` via `α ∈ (1−e)Rπ` and `πr(1−e) ∈ πR(1−e)`: `α·πr(1−e) = αr(1−e) = 1−e` and `πr(1−e)α = πrα = π`.
- By internal cancellation, `1−π ~ e`: choose `z ∈ eR(1−π)` and `z′ ∈ (1−π)Re` with `zz′ = e`, `z′z = 1−π`.
- Put `g = α + z`. Since `z = ez`, `g − a = −ea + z = e(z − a)`, so `g ∈ a + eR`.
- `(α+z)(r(1−e)+z′e) = αr(1−e) + αz′e + zr(1−e) + zz′e = (1−e) + 0 + 0 + e = 1`, because:
  - `αz′ = α(1−π)z′ = 0`;
  - `zr = z(1−π)r = z(r − rαr) = z(r − r(1−e)) = zre`, so `zr(1−e) = 0`.
- `(r(1−e)+z′e)(α+z) = rα + r(1−e)z + z′eα + z′ez = π + 0 + 0 + (1−π) = 1`, since `(1−e)z = 0` and `eα = 0`. ∎

**2. Unit-regularity.**
- Let `a = axa`, and replace `x` by `xax`, so also `x = xax`. Put `p = ax` and `q = xa`, both idempotents.
- `p ~ q` via `a ∈ pRq` and `x ∈ qRp`: `ax = p`, `xa = q`, `a = paq`, `x = qxp`.
- By internal cancellation, `1−q ~ 1−p`: choose `s ∈ (1−q)R(1−p)` and `t ∈ (1−p)R(1−q)` with `st = 1−q`, `ts = 1−p`.
- Put `v = x + s` and `v′ = a + t`:
  - `vv′ = xa + xt + sa + st = q + 0 + 0 + (1−q) = 1`;
  - `v′v = ax + as + tx + ts = p + 0 + 0 + (1−p) = 1`;
  - using `xt = xp(1−p)t = 0`, `sa = s(1−p)pa = 0`, `as = aq(1−q)s = 0`, `tx = t(1−q)qx = 0`.
- Finally `ava = axa + asa = a`, since `as = aqs = 0` (`a = aq` and `qs = 0`). ∎

**3. Import.** Camillo and Yu, *Exchange rings, units and idempotents*, Comm. Algebra 22 (1994) 4737–4749: an exchange ring has stable range one iff every von Neumann regular element is unit-regular. The statement is taken from arXiv:1402.4706 (§1, citing [4]); the primary theorem number was not checked at source. With part 2: if `R` is an exchange ring then `sr(R) = 1`.
