---
rg: 2
id: leavitt-packet-kernel-is-normally-generated-by-each-cycle
kind: claim
title: Every marked three-cycle normally generates the eight-word Leavitt kernel internally
distinct_from:
  leavitt-finite-wreath-targets-have-eight-tail-normal-form: That gives the explicit eight-tail realization criterion; this proves full nonidentity support in every target and internal normal generation by each individual tail.
  leavitt-eight-word-packet-is-quantitatively-equivalent: That compares the eight- and nine-row defects; this is an exact structural consequence of the shared coordinate equations and the local Thompson presentation.
artifacts:
  - research/artifacts/leavitt-eight-tail-full-support-and-normal-generation-2026-09-08.md
---

Let `Q=(C_3*C_2^3)/<<T_8>>`, let `N` be the kernel of its split
projection onto `C_2^3`, and put `c_x=b_x c b_x^-1` for `x in F_2^3`.
Then

```text
N=<<c_x>>_N       for every x in F_2^3.
```

Equivalently, every nontrivial homomorphism `N->G`, for any target
group `G`, retains all eight `c_x`. It is injective on each of the
eight indexed local Thompson subgroups `V_x<=N`.

The full eight-tail equations are a presentation of `N` on eight
generators with 72 relators. In any target group their solutions have
either zero or eight nonidentity tails. In particular supports of
sizes one through seven cannot give a witness in `V`.

No nontrivial solution in `V` is constructed. Internal normal generation
does not imply that `N` is simple: a proper kernel may avoid all the
local Thompson subgroups and contain mixed words among them.

DERIVATION
propagate-leavitt-tail-vanishing-across-two-faces
