---
rg: 2
id: random-coset-lamp-quotient-trace-proof
kind: route
title: Fold finite lamps onto every random coset space and test the identity coefficient
target: random-coset-lamp-quotient-is-regular-iff-irs-is-dirac
requires:
  - random-coset-lamp-correlations-realize-every-irs-character
  - zero-one-irs-character-is-normal-dirac
  - abelian-by-virtually-free-groups-are-sofic
---

Left translation on `V` makes `N_mu` invariant, because

```text
T_H(g.c)=g.T_H(c).                                      (RQP1)
```

Thus `(RCQ2)` is defined.  In the fiber

```text
W_H=(directSum_(Gamma/H) C_2) semidirect Gamma,
```

send `([c],g)` to the group element `(T_H(c),g)`.  Changing `c` by an
element of `N_mu` changes this field only on a null set, so these maps define
`rho_mu`.  If the resulting field is the identity almost everywhere, then
`g=e`; after that, `T_H(c)=0` almost everywhere, so `[c]=0`.  Therefore
`rho_mu` is faithful as an abstract group representation.

The canonical trace of `L(W_H)` is one precisely at the identity group
element.  Integrating over `H` gives `(RCQ4)`.  Since `[c]=0` exactly when
the event in `(RCQ4)` has probability one, regularity is equivalent to every
such event having probability zero or one.  Taking `c=e_e+e_g` gives
`(RCQ5)`, so regularity implies that `chi_mu` is zero-one valued.

Conversely, if `chi_mu` is zero-one valued, then
`zero-one-irs-character-is-normal-dirac` gives `mu=delta_K` for a normal
subgroup `K`.  Every parity-collapse event is then deterministic.  Its
probability is one exactly when `c in N_mu`, and zero otherwise, proving that
`(RCQ4)` is regular.

For the Manzoor actor, `Gamma` is a nonabelian free group.  Since `B_mu` is
countable abelian, `abelian-by-virtually-free-groups-are-sofic` applies to
`G_mu`.  Finally, in the Dirac case `T_K` identifies `B_mu` with
`directSum_(Gamma/K) C_2`; quotienting the actor by `K` produces `(RCQ6)` and
its literal actor subgroup is `Gamma/K`.  This proves the terminal recovery
statement.
