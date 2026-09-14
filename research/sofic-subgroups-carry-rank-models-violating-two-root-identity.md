---
rg: 2
id: sofic-subgroups-carry-rank-models-violating-two-root-identity
kind: claim
title: Every sofic group containing a dihedral D_8 has an F_2 rank model free on D_8, with rk((h-1)(g-1)) = 3/8
distinct_from:
  finite-subgroup-rank-data-cannot-force-two-root-identity: that is a per-finite-subgroup profile compatible with conjugation by the whole group; this is a genuine rank model of an arbitrary sofic subgroup, so no joint relation or rank inequality on a sofic subgroup, amenable and residually finite Kazhdan ones included, can force the root identity.
  rank-modelled-coefficients-violate-two-root-identities: that builds natural-tensor-natural models of EL_3 over coefficient rings with a rank model; this turns any sofic approximation of any group containing D_8 into a rank model that is free on D_8.
  monomial-rank-models-are-hamming-models: that shows monomial rank models are Hamming models, which rules them out for nonsofic hosts; this uses the permutation models of sofic subgroups to violate the matrix-unit identity.
artifacts:
  - research/artifacts/el3-two-root-identities-2026-09-12.md
---

Let `S` be a sofic group and `D = <g, h> <= S` dihedral of order `8`, with `g`, `h` involutions and
`gh` of order `4`. Let `phi_i : S -> Sym(n_i)` be a sofic approximation, and `P_i` its
permutation matrices over `F_2`. Then `sigma(a) = [P_i(a)]` is a homomorphism
`S -> M^x`, where `M = prod_omega M_(n_i)(F_2) / rank-null`, and

```text
rk( (sigma(h) - 1)(sigma(g) - 1) ) = 3/8 .
```

On `D`, `sigma` agrees with an honest free action on all but `o(n_i)` points.

**Consequence for the gate.** Let `R = L_(F_2)(1,2)`, `G = EL_3(R)`, and let `S <= G` be a sofic
subgroup containing `x_12(1)` and `x_23(1)`. Every property of `sigma|S` shared by all rank models
of `S` is compatible with `rk(N_23 N_12) = 3/8`. So a proof of
`rank-models-of-el3-satisfy-the-two-root-identities`, or of
`leavitt-el3-rank-models-over-finite-fields-are-trivial`, must use `sigma` jointly on a
**nonsofic** subgroup containing `x_12(1)` and `x_23(1)`. The following subgroups cannot carry the
argument:
- `UT_3(R)`, and `<diag(u, u^-1, 1), x_12(1), x_23(1)>` for any unit `u`, which lies in
  `UT_3(R) ⋊ Z` and so is solvable;
- level groups and `EL_3(A_inf)`, which are locally finite;
- residually finite Kazhdan subgroups such as `EL_3(F_2[s_0])`. The powers of `s_0` are linearly
  independent, so `F_2[s_0]` is a polynomial ring and `EL_3(F_2[s_0])` is finitely generated and
  linear over a commutative ring, hence residually finite.

Moreover, an argument that forces the identity on a subgroup `S` would at the same time prove
`S` nonsofic.

Proof: `research/artifacts/el3-two-root-identities-2026-09-12.md`, Section 6.4.
