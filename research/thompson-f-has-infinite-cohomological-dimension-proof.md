---
rg: 2
id: thompson-f-has-infinite-cohomological-dimension-proof
kind: route
title: Disjointly supported bumps give Z^n in Thompson's group F for every n
target: thompson-f-has-infinite-cohomological-dimension
requires: []
---

**Torsion-free.** Let `g` be an orientation-preserving homeomorphism of `[0,1]`
with `g != id`. Pick `x` with `g(x) != x`; replacing `g` by `g^-1` if needed,
`g(x) > x`. Since `g` is increasing, `g^(k+1)(x) > g^k(x)` for all `k >= 0`, so
`g^k(x) > x` and `g^k != id` for every `k >= 1`.

**Elements supported in a dyadic interval.** Let `J = [a, a + 2^-m]` with
`a = j 2^-m`, and let `α(t) = a + 2^-m t`, an affine map `[0,1] -> J` with slope
a power of 2 and dyadic offset. For `x0 ∈ F`, a non-identity element with
support `(0,1)`, define `b_J = α x0 α^-1` on `J` and the identity off `J`. Its
breakpoints are `α` of the breakpoints of `x0`, together with the endpoints of
`J`, all dyadic. Its slopes are those of `x0`, all powers of 2. It is a
homeomorphism of `[0,1]`, so `b_J ∈ F`, `b_J != id`, and its support is the
interior of `J`.

**`Z^n` inside `F`.** Choose pairwise disjoint dyadic intervals
`J_1, ..., J_n` (for example `J_k = [1 - 2^(1-k), 1 - 2^-k]`) and put
`b_k = b_(J_k)`. Elements with disjoint supports commute, so
`A = <b_1, ..., b_n>` is abelian. The map `Z^n -> A`,
`(m_1, ..., m_n) ↦ b_1^(m_1) ⋯ b_n^(m_n)`, is onto. It is injective: on `J_k` the
product restricts to `b_k^(m_k)`, which is the identity only when `m_k = 0` by
torsion-freeness. So `A ≅ Z^n`.

**Cohomological dimension.** If `H <= G` then `cd H <= cd G`: restricting a
projective resolution of `Z` over `ZG` to `ZH` gives a projective resolution
over `ZH`, since `ZG` is free over `ZH`. And `cd Z^n = n`: the torus `T^n` is a
`K(Z^n, 1)`, so `cd <= n`, and `H^n(Z^n; Z) ≅ Z != 0`, so `cd >= n`. Therefore
`cd F >= n` for every `n`, and `cd F = ∞`.
