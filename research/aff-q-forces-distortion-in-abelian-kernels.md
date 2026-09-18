---
rg: 2
id: aff-q-forces-distortion-in-abelian-kernels
kind: claim
title: In every finitely generated overgroup of Aff(Q), every abelian quotient kills a finitely generated subgroup with a distorted cyclic subgroup
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that is the open embedding problem; this is an obstruction lemma about every finitely generated overgroup of Aff(Q), hence of GL_n(Q) and SL_n(Q) for n >= 2.
  aff-q-does-not-embed-in-aut-thompson-f: that excludes T-bar and Aut(F) through Belk--Hyde--Matucci's Proposition 13 (every Q in T-bar contains the centre); this is a general statement about abelian quotients of arbitrary finitely generated overgroups, with no host fixed.
  germ-extensions-omit-standard-gl-n-q: that excludes the standard analytic copies of GL_n(Q) from piecewise-projective and piecewise-affine hosts; this constrains every copy of Aff(Q), standard or not, through the abelianization Q^x of Aff(Q).
  fg-pl-quasi-similarity-groups-contain-no-gl-2-q: that excludes Aff(Q) from finitely generated periodic PL quasi-similarity groups of the line by a scaling lemma; this is a host-free statement about abelian quotients of every finitely generated overgroup.
---

**ESTABLISHED** through `aff-q-forces-distortion-in-abelian-kernels-proof`
(elementary; lane proof, not independently reviewed; no priority claimed).

## Notation

For `a in Q^x` and `b in Q` write `D_a(x) = ax` and `T_b(x) = x + b`. For a
subgroup `K <= Q^x_{>0}` put `Aff_K(Q) = Q x| K = {x -> ax + b : a in K, b in Q}`.
`Aff^+(Q) = Aff_{Q^x_{>0}}(Q)` has index 2 in `Aff(Q)`.

## Statement

Let `K <= Q^x_{>0}` be a subgroup that is **not finitely generated**. Let `Gamma` be
a finitely generated group, `iota: Aff_K(Q) -> Gamma` an injective homomorphism, and
`phi: Gamma -> A` a homomorphism to an abelian group. Then:

1. There is `a in K`, `a != 1`, with `phi(iota D_a) = 0`; and `phi(iota T_b) = 0`
   for every `b in Q`.
2. So `ker phi` contains `H_a = <iota T_1, iota D_a>`. Write `a^(+-1) = p/q` in
   lowest terms with `p > q >= 1`. Then `iota T_1` has infinite order and
   `l_{H_a}((iota T_1)^(p^k)) <= 3 q^k` for every `k >= 1`. Hence `<iota T_1>` is
   distorted in the finitely generated group `H_a`: polynomially, with exponent
   `log q / log p < 1`, and logarithmically when `q = 1`.

**Corollaries.**
- **(i) Derived subgroup.** Taking `A = Gamma^ab`: the derived subgroup of every
  finitely generated overgroup of `Aff_K(Q)` contains a finitely generated
  subgroup with a distorted infinite cyclic subgroup.
- **(ii) Commensurated cyclic subgroups.** Let `z in Gamma` have infinite order,
  and suppose every `g in Gamma` commensurates `<z>`: there are nonzero integers
  `m, n` with `g z^m g^-1 = z^n`. If no finitely generated subgroup of
  `U_m C_Gamma(z^m)` has a distorted infinite cyclic subgroup, then `Aff_K(Q)`
  does not embed in `Gamma`.
- **(iii) Which groups.** `Aff^+(Q) <= Aff(Q) <= GL_2(Q)` (take `K = Q^x_{>0}`). The
  upper triangular matrices `[[a,b],[0,a^-1]]`, `a > 0`, in `SL_2(Q)` form a copy of
  `Aff_K(Q)` with `K = (Q^x_{>0})^2`, the squares, which is free abelian of
  infinite rank. The same subgroup maps injectively to `PSL_2(Q)`. So every
  statement above applies to `Aff(Q)`, `SL_2(Q)`, `PSL_2(Q)`, and to every group
  containing one of them, such as `GL_n(Q)`, `SL_n(Q)` and `B_n(Q)` for `n >= 2`.

## Scope

- This lemma is only about abelian quotients. It says nothing about `U_3(Q)`,
  which has no dilations. It also says nothing about `Q x|_a Z` for a single
  `a`, because there `K` is finitely generated.
- Application to commensurator-type hosts (Spark S1 of
  `research/artifacts/gq-gq-lit-q-embeddings.md` §7, and end-germ groups of finite
  germ extensions): `commensurating-end-germ-groups-omit-aff-q`. For groups of
  homeomorphisms of the whole line see `fg-pl-quasi-similarity-groups-contain-no-gl-2-q`
  (different proof).
