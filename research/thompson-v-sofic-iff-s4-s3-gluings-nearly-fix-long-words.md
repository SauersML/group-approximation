---
rg: 2
id: thompson-v-sofic-iff-s4-s3-gluings-nearly-fix-long-words
kind: claim
title: Thompson's V is sofic exactly when free gluings of an S4-set and an S3-set nearly satisfy four words
distinct_from:
  thompson-v-sofic-iff-not-permutation-stable: that identifies soficity of V with the failure of Bradford's permutation-stability properties for almost-homomorphisms of the whole group; this makes the finite subgroups <a,b> and <a,c> act exactly and freely, so the only unknown is one permutation commuting with a.
  thompson-f-sofic-iff-relator-system-unstable: that is the finitary relator form for F, whose almost-solutions must almost commute; this is a finitary form for V over the virtually free group S4 *_(C2) S3.
  thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3: that is the presentation fact this claim uses; this is the soficity statement.
---

**ESTABLISHED.** Use the generators `a = (00 01)`, `b = (01 10 11)`, `c = (1 00)` of Bleak--Quick
(2.4), acting on the right, and its four long words

```text
r5 = (cab^-1aba)^2 cb (cabab^-1a)^2
r6 = a(cb)^2 a(b^-1c)^2 bcabcb^-1cab^-1acb^-1(cb)^2 ab^-1
r7 = ab^-1cbc(ab^-1)^2 cbcb^-1a(b^-1c)^2 babcb^-1cab^-1
r8 = ca(b^-1c)^2 bacabacbc(b^-1ca)^2 b(cb^-1)^2(acb)^2 cb^-1cab^-1
```

A **free gluing** is a finite set `Y` with a free action of `S4 = <a, b | a^2, b^3, (ab)^4>` and a
free action of `S3 = <a, c | a^2, c^2, (ac)^3>` that agree on `a`. Equivalently, it is an action of
`S4 *_<a> S3` on which both factors act freely.

**Standard form.** Fix `L` divisible by 24. Let `a_0` be the pairing `x <-> x xor 1` of
`{0, ..., L-1}`, and let `b_0` and `c_0` be free `S4`- and `S3`-structures in which `a` acts as
`a_0`. Free `S4`-sets of equal size are isomorphic, and so are free `S3`-sets. So the free gluings
of size `L` are, up to isomorphism, exactly `(a_0, b_0, nu^-1 c_0 nu)` for `nu` in the centralizer
`C(a_0)`, which is `C2 wr S_(L/2)`.

The following are equivalent.
1. `V` is sofic.
2. For every `epsilon > 0` there is a free gluing on which each of `r5, ..., r8` fixes at least
   `(1 - epsilon)|Y|` points.
3. For every `epsilon > 0` there are `L` and `nu in C(a_0)` such that each `r_i(a_0, b_0, nu^-1 c_0 nu)`
   fixes at least `(1 - epsilon)L` points.

So `V` is not sofic exactly when some `epsilon_0 > 0` works for every `L` and every
`nu in C(a_0)`: one of the four words moves at least `epsilon_0 L` points.

## What it says

- **Short relators and separation are free of charge.** In every free gluing `a^2`, `b^3`, `(ab)^4`
  and `c^-1(ac)^2 a` hold exactly, and `a`, `b`, `c` move every point. All error sits in four words.
- **One unknown permutation.** The search space is `C2 wr S_(L/2)`, not triples of permutations.
- **Mechanism of `1 => 2`.** Finite groups are permutation stable with a linear rate. In a sofic
  approximation the rounded `S4`- and `S3`-actions are almost free. Two almost-equal free
  `a`-actions glue after padding by `o(L)` free orbits.
- **Mechanism of `2 => 1`.** The models define an almost-homomorphism of `V` in which `a` moves every
  point. Simplicity makes every nontrivial element separated, and diagonal powers amplify the
  separation.

Derivation: `thompson-v-sofic-iff-s4-s3-gluings-nearly-fix-long-words-proof`.
