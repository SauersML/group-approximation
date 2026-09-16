---
rg: 2
id: bengi-wise-groups-are-left-orderable-proof
kind: route
title: Both Bengi--Wise groups are doubles of left-orderable groups, and Promislow's group is not left-orderable
target: bengi-wise-groups-are-left-orderable
requires:
  - doubles-of-left-orderable-groups-are-left-orderable
  - promislow-group-is-not-left-orderable
artifacts:
  - research/artifacts/bengi-wise-doubles-left-orderable-2026-09-16.md
---

Artifact §§1, 3, 5. The certificate script is
`experiments/bengi-wise-double-abelianization-2026-09-16/snf.py` (md5
`9b2970c766767c760d3e16c869f6a65f`), and its output `snf.out` (md5
`3b7f36f95eba14913fd7ceb8ff88ed8a`) ends `ALLOK`.

## Part A: the groups are left-orderable

The source was read for two facts only. First, `F` is free on `a, b`
(l. 353). Second, `G` and `D(n)` are doubles in the sense of l. 184--186:
amalgams of a group with its copy along a subgroup, with the copy map as
gluing (l. 452 and l. 481--482). Nothing else about `\widehat H`,
`\widehat Y` or `n` is used.

1. `F` is free, so it is left-orderable by the consequences recorded in
   `doubles-of-left-orderable-groups-are-left-orderable`.
2. `G = F *_{\widehat H} \underline F` is a double of `F`, so `G` is
   left-orderable by `doubles-of-left-orderable-groups-are-left-orderable`.
3. `D(n) = G *_{\widehat Y} \underline G` is a double of `G`, so it is
   left-orderable by the same claim.
4. The same claim gives torsion-freeness, unique products, and the domain
   property of `k[D(n)]` for every field `k`. This is items 1 and 2.
5. A subgroup of `D(n)` isomorphic to `P` would carry the restricted left
   order. `promislow-group-is-not-left-orderable` excludes this. It applies to
   every subgroup of `D(n)`, including every finite-index subgroup, which is
   item 3.

**The source's main theorem fails.** Take the finite-index subgroup `D(n)`
itself. By item 3 it contains no copy of `P`, so `D(n)` does not persistently
contain `P` for any `n`.

## Part B: the failing step

Part B locates the error. It is not needed for Part A.

Let `K = <u, v | u^2 = v^2>` and `s = u^-1 v`.
- `u^2 = v^2` commutes with `u` and with `v`, so it is central.
- `u^-1 s u = u^-1 u^-1 v u = u^-2 v u = v^-2 v u = v^-1 u = s^-1`.
- So `u s u^-1 = u^-1 (u^2 s u^-2) u = u^-1 s u = s^-1`.
Put `T = <u^2, s>`.

**`T_i = T`.** The source takes `K_i = <c, \underline c>` with
`c = a^-i b^{n_i} a^i` to be a Klein bottle group (l. 455--457), so
`(u, v) = (c, \underline c)`. It displays
`T_i = <c^2, c \underline c^-1>` (l. 471--478). In `K`,
`c \underline c^-1 = u v^-1 = u s^-1 u^-1 = s`, so `T_i = <u^2, s> = T`.

**The honest double.** In `D(n)`, each `t in T_i ⊆ \widehat Y` is identified
with its copy. So the group the source embeds as `P_i` (l. 496--499) is
presented by

```text
< u, v, U, V | u^2 = v^2,  U^2 = V^2,  u^2 = U^2,  u^-1 v = U^-1 V >.
```

Its abelianization is `Z ⊕ (Z/2)^2`, by the Smith normal form in `snf.out`.
Independently, the fold retracts it onto `K`, and `K` maps onto `Z` via
`u, v -> 1`, so it is infinite.

The substitution `v = us`, `U = u t^-1`, `V = U s` turns it into
`<u, s, t | u^-1 s u = s^-1, u^-1 t u = t^-1, [s, t]>`, which is
`Z^2 x|_{-I} Z`.
- *Forward.* `u^-1 t u = u^-1 U^-1 u^2 = u^-1 U^-1 U^2 = u^-1 U = t^-1`,
  using `u^2 = U^2`. Also `t s t^-1 = U^-1 (u s u^-1) U = U^-1 s^-1 U = s`,
  where `U^-1 s U = s^-1` is the Klein relation of the second factor, since
  `U^-1 V = s`.
- *Backward.* The images of the four relators evaluate to the identity in the
  affine action of `<u, s, t>` on `R^3` given by
  `u : (x, y, z) -> (-x, -y, z + 1)` and translations `s = e_1`, `t = e_2`.
  The script checks this on words. The action is faithful: every element of
  `Z^2 x|_{-I} Z` has a normal form `s^m t^n u^k`, and that element moves the
  origin to `(±m, ±n, k)`.
- The two substitutions are mutually inverse on generators. For example,
  `V -> U s -> U u^-1 v`, which equals `V` by the gluing relation
  `u^-1 v = U^-1 V`.

**Promislow's group.** In `P = <a, b | ...>`:
- `K_a = <a, b^2>` is a Klein bottle group, with `a` inverting `b^2`;
- `K_b = <b, a^2>` is one too.
Both contain the torus `<a^2, b^2>`. The relations of `P` glue `u^2 = U^-1 V`
and `u^-1 v = U^2`. After `v = u U^2` and `V = U u^2`, the script finds that
the two remaining relators are cyclic conjugates of the relators of `P` or of
their inverses. The abelianization of `P` is `(Z/4)^2`.

`Z ⊕ (Z/2)^2` is not `(Z/4)^2`, so the honest double is not isomorphic to `P`.
The identification "`P = K *_T \underline K`" at l. 191, used at l. 499, is
therefore false for the gluing of l. 186.
