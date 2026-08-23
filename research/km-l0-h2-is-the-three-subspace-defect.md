---
rg: 2
id: km-l0-h2-is-the-three-subspace-defect
kind: claim
title: The lattice's second L0-cohomology is a three-subspace distributivity defect with vanishing pairwise part
artifacts:
  - research/artifacts/km-lattice-cohomology-and-lp-fork-2026-08-23.md
distinct_from:
  km-some-ergodic-action-has-nonzero-l0-second-cohomology: that is the open existence question across all ergodic actions; this is an established exact computation of the Bernoulli instance's H^2 as an explicit defect module, deciding nothing about its (non)vanishing yet.
  km-l0-cohomology-is-the-49-orbit-invariants-complex: that reduces H^(<=2) to the thick-part orbit complex for all divisible coefficients; this supersedes it for the Bernoulli L^0 module by running the isotropy spectral sequence on the contractible building itself, where local finiteness of parabolics kills every entry except (1,1).
  locally-finite-bernoulli-first-l0-cohomology-nonzero: that proves the ingredient groups are nonzero; this computes how they assemble into H^2.
---

**THEOREM (established; proof in
`km-l0-three-subspace-proof`).**  Let `Lambda = Lambda_(2,4,6)(q)`,
`q > 1764^3`, acting on its Bernoulli shift `Y = [0,1]^Lambda`, and
`V = L^0(Y, R)`.  Identify (injectively, by finite index over `B_-`
and unique divisibility) each `H^1(P_K^-, V)` with its stable image
`St_K` inside `H := H^1(B_-, V)`.  Then:

```text
(a) H^2(Lambda, V) = E_2^(1,1) of the isotropy spectral sequence on
    the contractible building X_-, the ONLY nonzero entry on its
    degree-two diagonal;

(b) St_j cap St_k = St_jk for all three vertex pairs (the pairwise
    defect vanishes: the obstruction module is the Levi-invariant
    rational cycle space of the rank-two polygon incidence graph,
    which flag-transitivity kills);

(c) H^2(Lambda, V) ~= ((St_1 + St_2) cap St_3) / (St_13 + St_23),
    the three-subspace distributivity defect;

(d) the defect is an extension whose kernel part is
    coker(H^1(Gamma_3, V) -> Hom(N_3, V)^Lambda) for
    Gamma_3 = P_13^- *_(P_3^-) P_23^- ->> Lambda with free kernel
    N_3, N_3^ab = H_1 of the cotype-3 subgraph of X_-.
```

Consequence: Ioana--Spaas--Wiersma Corollary E fires at the Bernoulli
action (hence `C*(Lambda)` fails the LP) IF AND ONLY IF this defect
module is nonzero -- the clause is now a single equivariant
computation, not a search over mechanisms.
