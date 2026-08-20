---
rg: 2
id: jacobi-congruence-clifford-tower
kind: claim
title: A finitely presented Jacobi congruence tower realizes the binary Clifford tape with fixed word templates
distinct_from:
  self-similar-clifford-quantum-expander-tape: that states the complete expander-tape interface; this isolates the remaining algebraic construction after relative property (T) supplies its spectral gap.
---

Construct a finitely presented group `Gamma` containing a Heisenberg-type
normal subgroup and fixed words `S`, together with nested finite quotients
`Gamma_n` and projective representations

```text
pi_n: Gamma -> PU((C^2)^(tensor r_n)),   r_n -> infinity,
```

such that:

1. the Heisenberg image has a common nontrivial central sign and acts by the
   irreducible binary Schrodinger representation;
2. the adjoint actions of the fixed words `S` normalize the Pauli group, so
   they are Clifford checks on every prefix;
3. the level shift and the inclusion of one new Pauli cell are represented by
   fixed group words with derivations of polynomial cost in the level;
4. the selector-controlled affine commutators of the Schur rank gate use the
   same central sign and commute with the old prefix as required; and
5. `(Gamma,N)` has a fixed relative Kazhdan pair for the Heisenberg normal
   subgroup `N` (or another fixed normal subgroup acting irreducibly in every
   `pi_n`).

By `relative-t-heisenberg-adjoint-quantum-expansion`, item 5 turns `S` into
uniform quantum expanders automatically. Items 1--4 then imply
`self-similar-clifford-quantum-expander-tape`.

## Attempts

The natural trial ring is `F_2[t]` with quotients `(t^n)`: its additive
quotients have binary size and a shift is built into multiplication by `t`.
However, relative property `(T)` for an elementary-linear semidirect product
does not by itself prove that the required central Heisenberg/Jacobi extension
is finitely presented, nor that characteristic-two Weil lifts and the nested
rank gates satisfy items 2--4. Those checks are part of this open claim.
