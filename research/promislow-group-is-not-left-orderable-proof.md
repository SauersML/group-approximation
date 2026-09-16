---
rg: 2
id: promislow-group-is-not-left-orderable-proof
kind: route
title: Inverting a Klein relation bounds every power of the inverted element, and the two bounds form a cycle
target: promislow-group-is-not-left-orderable
requires: []
artifacts:
  - research/artifacts/bengi-wise-doubles-left-orderable-2026-09-16.md
---

Artifact §4. Every step is a finite computation from the two defining
relations, and no literature is used.

**Lemma.** Let `<` be a left order on a group, and suppose `c^-1 s c = s^-1`
with `c > 1`. Then `s^k < c` for every `k in Z`.

*Proof.* Conjugation gives `c^-1 s^k c = s^-k`, so `s^k c = c s^-k` for all
`k`, and hence `s^-k c = c s^k`.
- If `s^k <= 1`, then `s^k < c`.
- If `s^k > 1`, suppose `c <= s^k`. Left-multiplying by `s^-k` gives
  `s^-k c <= 1`. But `s^-k c = c s^k`, and `c s^k > c > 1`: the first
  inequality is `1 < s^k` multiplied on the left by `c`. This is a
  contradiction. □

**Nontriviality.** The assignment `a -> (1,0)` and `b -> (0,1)` defines a
homomorphism `P -> (Z/4)^2`: the relator `b^-1 a^2 b a^2` has exponent sums
`(4,0)`, and `a^-1 b^2 a b^2` has `(0,4)`. So `a != 1` and `b != 1`.

**The relations survive inversion.**
- From `a^-1 b^2 a = b^-2`, conjugating again by `a` gives
  `a^-2 b^2 a^2 = a^-1 b^-2 a = (a^-1 b^2 a)^-1 = b^2`. So `a^2` commutes with
  `b^2`.
- Hence `a b^2 a^-1 = a^2 (a^-1 b^2 a) a^-2 = a^2 b^-2 a^-2 = b^-2`.
- The same computation with the roles of `a` and `b` exchanged gives
  `b a^2 b^-1 = a^-2`.
So `(a^e)^-1 b^2 a^e = b^-2` and `(b^f)^-1 a^2 b^f = a^-2` for all signs `e` and `f`.

**Proof of the claim.** Suppose `<` is a left order on `P`. Choose signs `e`
and `f` with `c := a^e > 1` and `d := b^f > 1`, which is possible since `a`
and `b` are nontrivial.
- The lemma with `(c, s) = (a^e, b^2)` gives `b^{2k} < c` for all `k`.
- The lemma with `(c, s) = (b^f, a^2)` gives `a^{2k} < d` for all `k`.
- Left-multiplying `1 < c` by `c` gives `c < c^2`, and `c^2 = a^{2e}` is a
  power of `a^2`, so `c^2 < d`.
- Likewise `d < d^2`, and `d^2 = b^{2f}` is a power of `b^2`, so `d^2 < c`.
Hence `c < c^2 < d < d^2 < c`, which is impossible. □
