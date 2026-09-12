---
rg: 2
id: corona-restricted-burnside-equals-power-law-moduli
kind: claim
title: Corona restricted Burnside is equivalent to finitely many dimension-free power-law moduli
distinct_from:
  corona-commuting-torsion-lifts: that lifts a COMMUTING countable torsion family in a corona to exactly commuting exact torsion matrices, and its finite exactification lemma is the abelian instance of the moduli below; this is an equivalence for arbitrary noncommuting exponent-N tuples, where no averaging into a finite abelian commutant is available.
  finite-group-corona-tail-exactification: that starts from a corona representation of a group already known to be FINITE and exactifies it on a cofinite tail; this is about corona subgroups whose finiteness is exactly what is in question, and it supplies no exactification.
  finite-group-opnorm-support-profile: that fixes a finite group and gives a dimension-free correction to an exact representation of it; this quantifies over an exponent rather than a group, and the number of power equations needed is not bounded in advance -- that gap is the whole content.
  mf-universal-horn-obstruction: that is one finite quasi-identity derived FROM the established non-MF theorem; this is a criterion whose input is a dimension-free matrix estimate and whose output would be new non-MF groups, so the implication runs the other way.
artifacts:
  - research/artifacts/opnorm-burnside-dossier-2026-08-24.md
---

Fix `m, N >= 2`, let `Q = (prod_n M_(d_n)) / (oplus_n M_(d_n))` range over
norm matrix coronas, and let `(RB1)` be the fixed finite presentation
`R(m,N) = <x_1..x_m | s_1..s_k>`.

The following are **equivalent**.

**(A) Corona restricted Burnside.**  For every matrix-size sequence
`d = (d_n)`, every `m`-generated subgroup `Gamma <= U(Q)` of exponent
dividing `N` is finite. Equivalently: every homomorphism
`B(m,N) -> U(Q)` factors through `R(m,N)`.

**(B) Finite dimension-free power-law moduli.**  For every relator `s_j` of
`(RB1)` and every `eps > 0` there are a **finite** set `W subset F_m` and
`eta > 0`, depending only on `m, N, s_j, eps`, such that for **every** `d`
and every `(U_1,...,U_m) in U(d)^m`,

```text
max_(w in W) || w(U_1,...,U_m)^N - I || < eta
   ==>   || s_j(U_1,...,U_m) - I || < eps.                       (PLM1)
```

No trace, no normalized Hilbert--Schmidt norm, no rank, no density and no
selected support occurs in `(PLM1)`; it is an implication between operator
norms in a single `M_d(C)`, with `W` and `eta` independent of `d`.

## Three readings of the same statement

**Kernel form.**  Put

```text
K_Q(m,N) = { r in F_m : r(u)=1 for every exponent-N tuple u in every corona },
K_fin(m,N) = ker(F_m -> R(m,N)).
```

Every exact finite-dimensional exponent-`N` representation factors through
`R(m,N)` (a f.g. periodic linear group is finite by Schur, and a finite
`m`-generated exponent-`N` group is a quotient of `R(m,N)`), so
`K_fin(m,N)` is precisely the exact finite-matrix kernel, and
`K_Q(m,N) <= K_fin(m,N)` always. The equivalence says the two statements
`(A)` and `(B)` both amount to

```text
K_Q(m,N) = K_fin(m,N).                                           (PLM2)
```

**Falsifiable fork.**  The proof of `(A) => (B)` is contrapositive and
*constructive*: failure of even one modulus manufactures, by diagonalization,
an honest exponent-`N` corona subgroup violating `s_j`. So this is an exact
fork, not a one-way sufficient condition -- a counterexample to `(B)` is an
operator-norm asymptotic periodic representation carrying strictly more group
theory than every exact finite-dimensional periodic representation.

**Sharpened target.**  It suffices to establish `(PLM1)` for a single
`eps < delta_N = 2 sin(pi/N)`. If the moduli hold at such an `eps`, then in
the corona `s_j(u)` lies in an exponent-`N` group and satisfies
`||s_j(u)-1|| <= eps < delta_N`, so
`finite-order-unitary-has-uniform-opnorm-gap` forces `s_j(u)=1`. Quantifying
over all `eps` is therefore not needed.
