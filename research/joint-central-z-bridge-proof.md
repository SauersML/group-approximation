---
rg: 2
id: joint-central-z-bridge-proof
kind: route
title: Use two half-flips and diagonalize in the sequence algebra
target: joint-central-z-bridge-forces-approximate-uniqueness
requires: []
---

## Proof

Since `rho(Z)` commutes with `phi(Z)`, nuclearity of `Z` gives a unital
homomorphism

```text
Theta_phi:Z tensor_min Z -> B_infinity,
Theta_phi(a tensor b)=phi(a)rho(b).
```

The approximate inner half-flip of `Z` supplies unitaries `w_m` in
`Z tensor Z` such that

```text
w_m(a tensor 1)w_m^* -> 1 tensor a                 (a in Z).
```

Thus `Theta_phi(w_m)` asymptotically conjugates the constant copy `phi` to
`rho` inside `B_infinity`.  Choose a dense sequence in the unit ball of `Z`
and diagonalize these unitaries: one obtains a unitary `V_phi in B_infinity`
with

```text
V_phi phi(a) V_phi^* = rho(a)                       (a in Z).       (1)
```

For completeness, the diagonalization has no lifting gap.  Every unitary of
`B_infinity` has a representative consisting of unitaries in `B`: an
arbitrary representative is asymptotically unitary and its tail can be
replaced by its polar part.  For the `m`th approximate conjugacy choose such
a representative; beyond a coordinate threshold it has error below `1/m`
on the first `m` dense elements.  Taking successive coordinate blocks from
these representatives gives (1).

The identical construction using commutation of `rho(Z)` with `psi(Z)` gives
a unitary `V_psi` satisfying

```text
V_psi psi(a) V_psi^* = rho(a).                      (2)
```

Therefore `V_psi^* V_phi` exactly conjugates the two constant embeddings in
`B_infinity`.  Represent it by unitaries `(u_n)` in `B`.  Equality in the
sequence quotient is precisely

```text
||u_n phi(a)u_n^* - psi(a)|| -> 0                   (a in Z),
```

which is approximate unitary equivalence in `B`.
