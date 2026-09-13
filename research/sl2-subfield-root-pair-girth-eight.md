---
rg: 2
id: sl2-subfield-root-pair-girth-eight
kind: claim
title: In SL_2(q^2), q even, the root subgroups u(F_q) and v(sF_q) with s outside F_q meet trivially and have coset graph of girth at least 10
---

Let `q = 2^f` and `k = F_q ⊂ F = F_{q^2}`, and let `s ∈ F \ k`. Put `u(a) = [[1,a],[0,1]]` and
`v(b) = [[1,0],[b,1]]` in `SL_2(F)`, and

```text
E = u(k) = { u(a) : a ∈ k },    E' = v(sk) = { v(sb) : b ∈ k },    both ≅ (Z/2)^f .
```

**ESTABLISHED.**
- (a) `E ∩ E' = 1`.
- (b) The coset graph `Γ_A(E, E')` has girth at least `10`, for `A = <E, E'>` or any finite group
  containing it. (The id predates the girth-10 argument; girth at least 8 was the first version.)
- (c) More generally, for any additive subgroups `L, L'` of any field of characteristic 2, `u(L)` and
  `v(L')` have girth at least `6`.

**Computed: the bound is sharp.** The girth is exactly `10` for `q = 4` (`s` primitive), and for `q = 8, 16`
with `s` in either Frobenius class (`experiments/sl2-root-triangle-kazhdan/run1.out`, `run2.out`). The
closed-walk counts `W_8 = 2092, 44248, 807856` for `q = 4, 8, 16` equal the tree counts
`14q^4 - 28q^3 + 20q^2 - 5q`, as girth at least 10 requires.

**Generation** for `q >= 32` follows from `sl2-subfield-root-links-codistance-large-q`. For `q = 8, 16` it
follows from `sl2-subfield-root-links-codistance-q8-q16`.

Proof of (a)–(c): `sl2-subfield-root-pair-girth-eight-proof`.
