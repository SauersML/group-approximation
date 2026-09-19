---
rg: 2
id: unit-alexander-singular-slice-contains-non-rf-bs-groups-proof
kind: route
title: A Nielsen change of basis turns the Magnus word into a Baumslag-Solitar relator times a free letter, and the Magnus vertex group embeds
target: unit-alexander-singular-slice-contains-non-rf-bs-groups
requires:
  - unit-alexander-singular-hidden-free-pieces-special
  - length19-singular-relators-z-stable-hierarchy-special
artifacts:
  - experiments/one-relator-bs-in-slice-2026-09-18/family.py
  - experiments/one-relator-bs-in-slice-2026-09-18/family.out
  - experiments/one-relator-bs-in-slice-2026-09-18/bs_search.py
  - experiments/one-relator-bs-in-slice-2026-09-18/verify.py
  - experiments/one-relator-bs-in-slice-2026-09-18/canon_counts.py
  - experiments/one-relator-bs-in-slice-2026-09-18/n2w7.out
  - experiments/one-relator-bs-in-slice-2026-09-18/n2w7.err
  - experiments/one-relator-bs-in-slice-2026-09-18/n2w7.verify
  - experiments/one-relator-bs-in-slice-2026-09-18/n2w7.counts
---

The slice and the Magnus conventions are those of
[[unit-alexander-singular-hidden-free-pieces-special]] and
[[length19-singular-relators-z-stable-hierarchy-special]].

## Proof

Fix `k >= 1` and write `T = a_2 a_0 a_1 a_2`. Then

`W_0 = a_2 a_0 a_1 a_2 . a_0^(-k) . a_2^(-1) a_1^(-1) a_0^(-1) a_2^(-1) . a_0^(k+1)`.

This is the Magnus word of the height sequence
`(2,1),(0,1),(1,1),(2,1),(0,-k),(2,-1),(1,-1),(0,-1),(2,-1),(0,k+1)`, closed cyclically at height 2.
Its `t`-moves have total length 16 and its `a`-exponents have total absolute value `9 + 2k`, so
`|w_k| = 25 + 2k`. The word is reduced and cyclically reduced: consecutive letters are at different
heights, and the last block `a_0^(k+1)` sits next to the first letter `a_2`.

**Step 1: slice membership.** Read cyclically, the level-0 syllables are `a_0, a_0^-k, a_0^-1, a_0^(k+1)`,
with sum `1`. The level-1 syllables are `a_1, a_1^-1`, with sum `0`. The level-2 syllables are
`a_2, a_2, a_2^-1, a_2^-1`, with sum `0`. So exactly one level has a non-zero sum and it is `1`: the
Alexander polynomial is a unit. Level 2 is a singular extreme. Both extremes have four syllables, so
neither is peelable. The `t`-exponent is 0 by construction. `verify.py` checks all of this
mechanically. It also checks that `census.cert_word`, the landed PEEL/PP/R1/CYC certificate search
run with budget 4000, finds no certificate for `w_k`. For `k = 1..8` this is
`python3 family.py 8 > family.out; python3 verify.py < family.out`, which prints `checked 8 failed 0`.
The census failure is only a computational fact about those certificates. The theorem does not use
it, beyond showing that `G_k` really lies in the open part of the slice.

**Step 2: basis change.** `a_1 = a_0^-1 a_2^-1 T a_2^-1`, so `T, a_0, a_2` generate
`F(a_0,a_1,a_2)`. A generating triple of a free group of rank 3 is a basis (free groups are Hopfian).
In this basis `W_0 = T a_0^(-k) T^(-1) a_0^(k+1)`, so

`B_0 = <a_0,a_1,a_2 | W_0> = <a_0, T | T a_0^k T^-1 = a_0^(k+1)> * <a_2> = BS(k,k+1) * Z`.

**Step 3: embedding.** `W_0` involves both `a_0` and `a_2`, the minimal and maximal levels. By
Magnus–Moldavanskii, `G_k = <B_0, t | t a_i t^-1 = a_(i+1), i = 0,1>` is an HNN extension of `B_0`.
Its associated subgroups `<a_0,a_1>` and `<a_1,a_2>` are free of rank 2 by the Freiheitssatz, and
`psi` maps one isomorphically onto the other. By Britton's lemma, `B_0` embeds in `G_k`. Hence
`BS(k,k+1)` embeds in `G_k`.

**Step 4: consequences.**
- **Torsion-free.** `B_0` is torsion-free, being a free product of an HNN extension of `Z` and `Z`.
  So `W_0` is not a proper power in `F(a_0,a_1,a_2)`: a one-relator group on a proper power has
  torsion. Therefore `w_k` is not a proper power either, since a root `u` of `w_k` would have
  `t`-exponent 0 and its Magnus word would be a root of `W_0`. So `G_k` is torsion-free.
- **`pi(w_k) = 2`.** `pi(w) = 1` exactly when `w` is a proper power, which is excluded. `w_k` is not
  primitive, because then `G_k = Z`, which has no `BS(k,k+1)` subgroup. A non-primitive element of
  `F_2` has `pi <= 2`. So `pi(w_k) = 2`.
- **Not hyperbolic.** In a hyperbolic group, an infinite-order `x` with `x^p` conjugate to `x^q`
  forces `|p| = |q|`. Here `a_0^k` is conjugate to `a_0^(k+1)`.
- **Not virtually special.** Suppose a finite-index `H < G_k` embeds in a right-angled Artin group
  `A`. Choose `m, j >= 1` with `b = a_0^m` and `s = T^j` in `H`. Iterating the BS relation gives
  `s b^(k^j) s^-1 = b^((k+1)^j)`. `A` acts properly and cocompactly on the CAT(0) universal cover of
  its Salvetti complex, so every infinite-order element acts as a hyperbolic isometry. Its
  translation length `tau` satisfies `tau(x) > 0`, `tau(x^n) = |n| tau(x)`, and is invariant under
  conjugation. That gives `k^j tau(b) = (k+1)^j tau(b)` with `tau(b) > 0`, a contradiction.
- **`k >= 2`: not residually finite and not linear.** By Meskin, `BS(m,n)` is residually finite
  only if `|m| = |n|`, or `|m| = 1`, or `|n| = 1`. So `BS(k,k+1)` is not residually finite, and
  neither is its overgroup `G_k`. By Mal'cev, finitely generated linear groups are residually finite.

This proves the theorem.

## The census

`bs_search.py NMAX WMAX LMAX "p,q ..."` runs a BFS over Nielsen bases `(U, V, X..)` of
`F(a_0..a_NMAX)` of total length at most `WMAX`, starting from the letter basis. For each pair with
`V` of unit exponent vector and each `(p,q)`, it forms `W_0 = U^-1 V^p U V^-q`. It keeps `W_0` if it
comes from a cyclically reduced `w` of length at most `LMAX` in the slice, and if `census.cert_word`
fails on it. Every such `B_0` is `BS(p,q) * F`, and it embeds as in Step 3.

Reproduction, from the experiment directory:
```
nice -n 10 python3 bs_search.py 2 7 45 "1,2 2,3 3,4" > n2w7.out 2> n2w7.err
python3 verify.py < n2w7.out > n2w7.verify      # checked 7392 failed 0
python3 canon_counts.py 2 < n2w7.out > n2w7.counts
```
`verify.py` shares no code with `bs_search.py`. It certifies each basis by greedy Nielsen reduction
to single letters, and it recomputes the Magnus word from `w` itself. The counts up to the census
symmetries (height reversal, inversion, `a -> a^-1`, cyclic rotation) are 288, 216 and 216 classes, with
minimum lengths 27, 29 and 31 for `BS(1,2)`, `BS(2,3)` and `BS(3,4)`. The search is exhaustive only
within its basis-length bound. It does not show that the slice has no BS subgroups at lengths 23 and
25.
