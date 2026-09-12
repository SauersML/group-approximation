---
rg: 2
id: stw11-clopen-exhaustion-proof
kind: route
title: Turn invariant compact-open support cuts into a central projectional approximate unit
target: stw11-clopen-exhaustion-glues-qd
requires:
  - stw09-local-mf-corner-traces-across-qd-extension-force-qd
  - tww-gabe-schafhauser-af-embedding-theorem
artifacts:
  - research/artifacts/stw99-xi-clopen-support-gluing-2026-08-30.md
---

Write

`A=C(X) rtimes Z^d`,  `I=C_0(U) rtimes Z^d`,
`B=C(Y) rtimes Z^d`.

Amenability of `Z^d` identifies full and reduced crossed products and gives
the exact sequence

`0 -> I -> A -> B -> 0`.                                      `(CE1)`

For each `n`, put `p_n=1_(K_n)`.  A compact-open subset of the open set
`U` is open in `X` and compact, hence also closed in `X`; thus
`p_n in C(X)`.  Invariance gives `u_g p_n u_g^*=p_n` for every
`g in Z^d`.  Therefore `p_n` is central in `A`, not merely quasicentral.

The projections form an approximate unit for `I`.  Indeed, for
`f in C_0(U)`, compactness of the level sets of `|f|` and the increasing
open cover `union K_n=U` give `||(1-p_n)f||->0`.  The same conclusion for
the dense algebraic crossed product, and then by contractivity for all of
`I`, shows that `(p_n)` is an increasing approximate unit.  Moreover,

`p_n A p_n = C(K_n) rtimes Z^d`.                              `(CE2)`

Thus `(CE1)` has an increasing quasicentral approximate unit of projections,
all its nonzero corners in `(CE2)` are quasidiagonal by hypothesis, and its
quotient is quasidiagonal.  Apply
`stw09-local-mf-corner-traces-across-qd-extension-force-qd` to conclude that
`A` is quasidiagonal.

For the mixed corollary, stable finiteness passes from `A` to its ideal
`I`.  The ideal is separable and exact, so Gabe's traceless AF-embedding
theorem makes `I` AF-embeddable and hence quasidiagonal.  Its corners
`p_n A p_n=p_n I p_n` are therefore quasidiagonal.  On the quotient, a
full-support invariant probability measure `mu` makes
`mu after E_Y` a faithful amenable trace.  The transformation-group
crossed product is separable, nuclear, and UCT; hence the
Tikuisis--White--Winter/Gabe/Schafhauser theorem makes it AF-embeddable and
in particular quasidiagonal.  The one-step result now applies.  Notice more
strongly that every bounded trace on `A` vanishes on `I`: its restriction is
a bounded lower-semicontinuous tracial weight on the traceless ideal, hence
can take only the value zero.  Thus, when `I!=0`, this argument cannot be a
disguised application of the global faithful-trace theorem.

For the finite filtration, apply the one-step argument first to
`Y_(s-1) supseteq Y_s`, then successively to
`Y_(s-2) supseteq Y_(s-1),...,Y_0 supseteq Y_1`.  At each step the newly
proved quasidiagonality is exactly the quotient hypothesis needed at the
preceding step.  This downward induction proves the stated conclusion.
