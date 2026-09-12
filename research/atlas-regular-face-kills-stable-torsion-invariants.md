---
rg: 2
id: atlas-regular-face-kills-stable-torsion-invariants
kind: claim
title: The regular Atlas face is cofinally real and kills every stable finite-torsion invariant
distinct_from:
  atlas-phase-cycle-determinant-is-gauge-trivial: that cancels determinants on the twenty-seven transported phase edges; this treats the full six-word regular microstate face and adds conjugate realification, Frobenius--Schur, and stable K-torsion cancellation.
  additive-index-instability: that gives the general warning that additive parity is killed by amplification; this proves that the exact Atlas defect and five-row payload are unchanged by the required amplification and constructs a real orthogonal representative at twice the multiplicity.
  atlas-full-relator-data-factor-through-double-commutant-gauge: that quotients left and right chart-commutant changes at one multiplicity; this uses block sum and complex conjugation to pass between multiplicities.
  fixed-rank-index-authenticator-has-gap-or-functoriality: that treats hard ranks and determinants of fixed matrix-polynomial blocks; this proves exact cancellation of stable finite-order classes on the specific regular two-A8 face before any continuity estimate is attempted.
---

**ESTABLISHED AMPLIFICATION/CANCELLATION FENCE.**  Put `d=20160` and use
real permutation matrices for the regular representation

```text
rho_k = k Reg(A8):A8 -> O(dk).
```

For the regular Atlas energies `A_k,B_k` of
`atlas-five-row-lift-failure-dichotomy`, block sum and complex conjugation
satisfy

```text
A_(k+l)(U directSum V)
  =(k A_k(U)+l A_l(V))/(k+l),
B_(k+l)(U directSum V)
  =(k B_k(U)+l B_l(V))/(k+l),                 (ATK1)

A_k(conjugate(U))=A_k(U),
B_k(conjugate(U))=B_k(U).                     (ATK2)
```

Consequently every positive-energy low-defect face

```text
Omega_k(eta,a)={U:B_k(U)<=eta^2, A_k(U)>=a}
```

is closed under arbitrary amplification:

```text
U in Omega_k(eta,a)  =>  U^(directSum m) in Omega_(mk)(eta,a). (ATK3)
```

It is also cofinally real.  There is a fixed block-scalar unitary `S`,
commuting with `rho_k directSum rho_k`, for which

```text
R(U)=S (U directSum conjugate(U)) S^*
```

is the ordinary realification of `U`, hence belongs to `O(2dk)`.  Equations
`(ATK1)--(ATK2)` give

```text
R(U) in Omega_(2k)(eta,a).                            (ATK4)
```

Thus a complex or quaternionic Frobenius--Schur obstruction cannot exclude
the regular face: both chart restrictions already have real forms, and the
whole relative tuple has a real form after one payload-preserving doubling.

There is an exact determinant statement as well.  For `g in A8`,

```text
g |-> det(Reg(g))
```

is a one-dimensional character of the perfect group `A8`, hence is trivial.
Therefore for every `k`, every relative unitary `U`, and every word
`w in A8*A8`,

```text
det(pi_U(w))=1.                                      (ATK5)
```

In particular the determinant line of each of the six Atlas word equations
is identically trivial, not merely small at low defect.  The determinant of
every exterior power is also trivial because

```text
det(exterior^r pi_U(w))
  =det(pi_U(w))^(binomial(dk-1,r-1))=1.               (ATK6)
```

Finally let `kappa` be any stable, unitary-conjugacy-invariant class attached
to this finite tuple, additive under block sum, and taking values in a finite
abelian group `T` of exponent `e`.  This includes parity, determinant-line
torsion, and finite-order K-theoretic pairings whenever those pairings are
defined.  By `(ATK3)`,

```text
kappa(U^(directSum e))=e kappa(U)=0                  (ATK7)
```

on another point of the same `Omega(eta,a)` face.  If conjugation reverses
the class, `(ATK4)` already cancels it in two copies.

Hence none of determinant-line parity, Frobenius--Schur type, exterior-power
determinant parity, or stable finite K-torsion can prove a zero-versus-nonzero
obstruction uniform in regular multiplicity.  Any surviving K-theoretic
route must produce an **infinite-order positive-density** pairing that is not
removed by realification; moreover it must be controlled from normalized-HS
relator defect, which is precisely the additional coercivity absent from a
bare topological class.

## Attempts

- **Use the determinant of a relator word.**  It is exactly one by `(ATK5)`
  before any relator is imposed.
- **Pass to determinant lines of exterior powers.**  Formula `(ATK6)` keeps
  them exactly trivial.
- **Use real/quaternionic representation parity.**  Conjugate doubling gives
  the real orthogonal model `(ATK4)` without reducing five-row energy.
- **Use a finite K-theory or parity class.**  Amplification by its exponent
  kills the class while leaving `A_k` and `B_k` unchanged.
