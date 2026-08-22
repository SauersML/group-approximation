---
rg: 2
id: finite-character-orbits-detect-module-residual
kind: claim
title: Finite character orbits detect exactly the finite residual of a finite-field actor module
distinct_from:
  infinite-character-actor-kills-fd-mark: that assumes every seed-visible character orbit is infinite; this identifies that assumption algebraically and constructs an exact marked finite-dimensional representation whenever it fails by residual finiteness.
  finite-covariance-energy-sees-only-character-restrictions: that gives approximate two-block swaps invisible to finitely many evaluations; this gives an exact finite actor-invariant spectral packet from a finite module quotient.
  finite-type-linear-vfree-envelope-is-residually-finite: that proves residual finiteness for one class of modules; this is the general dual equivalence between module residual finiteness and finite character orbits.
---

Let `A` act linearly on an `F_p`-module `M`, and fix `m in M`.  The
following are equivalent.

1. There is a finite `A`-module `Q` and an `A`-equivariant linear map
   `q:M->Q` with `q(m)!=0`.
2. There is an additive character `chi:M->mu_p` whose `A`-orbit is finite
   and for which `chi(m)!=1`.

Consequently the vectors annihilated by every finite-orbit character are
exactly the finite residual

```text
intersection_(q:M->Q finite A-module) ker(q).           (FCRD1)
```

For `p=2`, if `m_0` survives a finite `A`-module quotient, then the Pauli
seed extension of `M semidirect A` with involutions `z,J` and

```text
J central,                 [m_0,z]=J                    (FCRD2)
```

has an exact finite-dimensional representation with `J=-I`.  Hence the
aperiodicity hypothesis used by the infinite-character actor route is not
merely stronger than residual finiteness: a marked residually finite module
supplies an exact finite-dimensional countermodel to the desired central-mark
annihilation.

The implication from a finite quotient is elementary.  Choose
`ell in Q^*` with `ell(q(m))!=0` and compose `ell q` with a fixed nontrivial
additive character of `F_p`.  Its orbit lies in the finite set `Q^*`.

Conversely, if the orbit `O=A chi` is finite, the evaluation map

```text
Phi:M -> F_p^O,        Phi(x)=(eta(x))_(eta in O)       (FCRD3)
```

is `A`-equivariant after identifying `mu_p` with the additive group of
`F_p`.  Its finite image separates `m` because the `chi` coordinate does.

For the final assertion take a finite quotient `Q` retaining `m_0`, choose
`alpha in Q^` with `alpha(q(m_0))=-1`, and work on `ell^2(Q^)`.  Let `M`
act by the character multipliers

```text
(rho(m)xi)(eta)=eta(q(m))xi(eta),                       (FCRD4)
```

let `A` permute `Q^` by its dual action, let `z` translate `Q^` by
`alpha`, and put `J=-I`.  The quotient map is equivariant, so these operators
represent `M semidirect A`; translation by `alpha` anticommutes with the
multiplier for `m_0`, proving `(FCRD2)` exactly.

