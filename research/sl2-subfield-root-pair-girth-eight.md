---
rg: 2
id: sl2-subfield-root-pair-girth-eight
kind: claim
title: In SL_2(q^2), q even, the root subgroups u(F_q) and v(sF_q) with s outside F_q meet trivially and have coset graph of girth at least 8
---

Let `q = 2^f` and `k = F_q ⊂ F = F_{q^2}`, and let `s ∈ F \ k`. Put `u(a) = [[1,a],[0,1]]` and
`v(b) = [[1,0],[b,1]]` in `SL_2(F)`, and

```text
E = u(k) = { u(a) : a ∈ k },    E' = v(sk) = { v(sb) : b ∈ k },    both ≅ (Z/2)^f .
```

**ESTABLISHED.**
- (a) `E ∩ E' = 1`.
- (b) The coset graph `Γ_A(E, E')` has girth at least `8`, for `A = <E, E'>` or any finite group
  containing it.
- (c) More generally, for any additive subgroups `L, L'` of any field of characteristic 2, `u(L)` and
  `v(L')` have girth at least `6`.

**Computed, not needed for (b).** The girth is exactly `10` for `q = 4` (`s` primitive), and for
`q = 8, 16` with `s` in either Frobenius class
(`experiments/sl2-root-triangle-kazhdan/run1.out`, `run2.out`).

**Generation.** For `q >= 4` one expects `<E, E'> = SL_2(F)`: by Dickson's classification the only
candidates would be conjugates of `SL_2(q)`, and those are excluded because the subline through `0` and
`∞` stable under `u(k)` is `P^1(k)`, which `v(sk)` does not preserve. Dickson's theorem was not re-read,
so general generation is **not** established here. For `q = 8, 16` it follows from the certified gap
`σ_2 < 1` in `sl2-subfield-root-links-codistance-q8-q16`.

Proof of (a)–(c): `sl2-subfield-root-pair-girth-eight-proof`.
