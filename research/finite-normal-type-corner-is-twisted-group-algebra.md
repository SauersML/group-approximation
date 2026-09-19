---
rg: 2
id: finite-normal-type-corner-is-twisted-group-algebra
kind: claim
title: An invariant irreducible finite-normal-subgroup corner is a matrix algebra over a finite-phase twisted group algebra
distinct_from:
  unique-trace-signed-corner-quotient-forces-nonhyperlinear: that promotes a quotient trace abstractly; this computes the complete algebra and canonical trace of the finite-normal signed corner before any quotient is chosen.
  twisted-factor-existence-is-equivalent-to-nonhyperlinearity: that is an existence equivalence for non-CE twisted factors; this is the Clifford decomposition showing that every invariant finite-type signed corner is already one such twisted algebra after removing a matrix factor.
---

Let `K` be a finite normal subgroup of a countable group `Gamma`, and let
`rho in Irr(K)` have `Gamma`-invariant equivalence class.  If `d=dim(rho)`,
`q=z_rho`, and `Q=Gamma/K`, then there is a finite-valued scalar two-cocycle
`omega` on `Q` such that

```text
q C*(Gamma) q ~= M_d(C) tensor C*_omega(Q).              (FTC1)
```

The isomorphism sends the normalized canonical corner trace to

```text
tr_d tensor tau_omega.                                   (FTC2)
```

Indeed `D=qC[K]q` is `M_d(C)`.  Each `Q`-homogeneous fibre of
`qC[Gamma]q` is a rank-one `D`-bimodule.  After multiplying a coset
representative by a unitary in `D`, choose a unitary `y_x` centralizing `D`.
Then Schur's lemma gives

```text
y_x y_y=omega(x,y)y_(xy).
```

The fibre decomposition proves the algebraic isomorphism
`D tensor C_omega[Q] ~= qC[Gamma]q`, and universal completion gives `(FTC1)`.
The Mackey/Clifford obstruction comes from the finite group `K`; its class is
torsion and admits a root-of-unity-valued representative.  Distinct
`K`-cosets are orthogonal for the canonical group trace, while its normalized
restriction to `D` is `tr_d`, proving `(FTC2)`.

Full details and the finite-phase reduction are in
`research/artifacts/finite-type-corner-clifford-collapse-2026-08-21.md`.
