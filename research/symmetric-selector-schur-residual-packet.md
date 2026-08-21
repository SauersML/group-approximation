---
rg: 2
id: symmetric-selector-schur-residual-packet
kind: claim
title: A symmetric selector power packages every Schur residual congruence in one primitive finite type
distinct_from:
  selector-correlated-direct-power-router: that uses one coordinatewise inner automorphism and a balanced HNN word to cancel arbitrary multiplicity action; this uses a finite symmetric semidirect product so all selector sectors and reset translations already lie in one primitive finite-group type.
  four-point-gauge-orbit-has-balanced-derived-rank-swap: that supplies the one-pair rank swap on four gauge points; this packages the rank-fifteen residual forms and makes every selector translation derived, but does not yet compute the final restriction matrix after adjoining that rank swap.
---

Let `X=F_2^4`.  For every `x in X`, let `B_x` be the nondegenerate
rank-fifteen residual pairing supplied by
`fanizza-schur-menu-has-common-codimension-one-residual`.  Let `H_x` be the
extraspecial group whose two preferred elementary abelian halves have
commutator pairing `B_x`.  Fix one standard extraspecial group

```text
H=<J,p(u),q(v) | [p(u),q(v)]=J^(u dot v)>,             (SSP1)
```

with `u,v in F_2^15`, and let `rho` be its unique `J=-1` spin
representation.  Choose isomorphisms

```text
phi_x:H -> H_x.                                        (SSP2)
```

They implement fixed left-right congruences from the standard pairing to
`B_x` and exist because the associated full alternating commutator forms are
isometric.

Put

```text
G=(product_(x in X) H_x) semidirect Sym(X),            (SSP3)
```

where a permutation sends `H_x` to `H_(pi x)` through
`phi_(pi x) phi_x^(-1)`.  Let `sigma_x` be the representation of the base
product which uses `rho phi_x^(-1)` on the `x`-factor and the trivial
representation on every other factor.  The orbit sum

```text
Sigma=direct_sum_(x in X) sigma_x                      (SSP4)
```

extends to one irreducible representation of `G`: equivalently, extend
`sigma_0` trivially across the point stabilizer `Sym(X\{0})` and induce to
`G`.  Its restriction to the base product is `(SSP4)`, with every `sigma_x`
occurring once.  Hence one primitive central idempotent `e_Sigma in C[G]`
selects a finite type in which all sixteen residual spin packets occur with
exactly the same multiplicity.

Write `J_x` for the central sign in the `x`-factor and define

```text
J_all=product_x J_x,
z_i=product_(x:x_i=1) J_x,             1<=i<=4.         (SSP5)
```

On the `sigma_x` summand,

```text
J_all=-1,                    z_i=(-1)^(x_i).            (SSP6)
```

Thus the simultaneous selector eigenspaces inside the single primitive type
`Sigma` are precisely its sixteen summands.

The twisted permutation action fixes pointwise the standard diagonal copy

```text
Delta(H)={(phi_x(h))_x:h in H}.                         (SSP7)
```

The preferred `B_x`-labelled halves in `H_x` are related to this common
diagonal packet by the fixed congruence `phi_x`; all of those label changes
are therefore part of one finite multiplication table.  A selector
translation carries the `x`-labelled residual to the `(x+v)`-labelled
residual through the chosen congruence, while acting on the spin factor by
the corresponding exact intertwiner.  No HNN multiplicity unitary and no
unselected packet type occurs.

For a nonzero reset direction `v in X`, let `tau_v in Sym(X)` be translation
`x |-> x+v`.  Then

```text
tau_v J_all tau_v^(-1)=J_all,
tau_v z_i tau_v^(-1)=J_all^(v_i) z_i.                  (SSP8)
```

Moreover `tau_v` is an ordinary commutator in `Sym(X)`, hence in `[G,G]`.
Indeed choose `u` independent of `v`; on every four-point coset of
`span(u,v)`, choose two square reflections whose commutator is the half-turn
`x |-> x+v`, and take their products over the four cosets.  Those reflection
permutations commute with the constant diagonal residual `Delta(H)`.  The
reset is therefore simultaneously:

1. the required gauge translation on the selector signs;
2. a derived ordinary word; and
3. central relative to the common standard residual packet.

All groups and tables in `(SSP1)--(SSP8)` are fixed and finite.  Consequently
finite-group Hilbert--Schmidt exactification gives a dimension-independent
robust version on the `e_Sigma` carrier.  Arbitrary ambient multiplicity is a
single tensor factor common to all sixteen selector summands, rather than a
new mode for each sector.

## Claim boundary

This closes the **finite packaging** of the rank-fifteen congruence menu and
the derivedness of every selector translation.  It does not yet prove
`derived-lifted-gauge-reset-spin-bridge`: the restriction matrix obtained
after coupling the four-point balanced rank-swap packet to `Sigma` must still
be checked to give the old baseline and reverse reset edge types with equal
multiplicity.  That remaining question is a finite branching calculation,
not an unbounded selector-router or multiplicity-unitary problem.
