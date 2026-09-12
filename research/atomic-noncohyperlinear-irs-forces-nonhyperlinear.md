---
rg: 2
id: atomic-noncohyperlinear-irs-forces-nonhyperlinear
kind: claim
title: An atomic non-co-hyperlinear IRS already yields a non-hyperlinear group
distinct_from:
  non-cohyperlinear-irs-exists: that supplies a non-CE IRS character but does not control whether its ergodic law has atoms; this proves that any atom would already finish the group problem.
  diracization-gap-equals-nonhyperlinear-group: that intersects independent IRS samples and asks whether non-CE survives to the normal core; this uses one finite conjugacy orbit and finite-index induction, with no limiting operation.
  finite-index-induction-transfers-non-ce-factor: that transports a named factor representation upward through finite index; this identifies the representation attached to an atomic IRS as precisely such an induction and extracts a canonical quotient group factor from the ambient matrix algebra.
---

Let `mu` be an ergodic invariant random subgroup of a countable group
`Gamma`.  If `mu` has an atom and its IRS character

```text
chi_mu(g)=mu({H:g in H})                                (ANI1)
```

has non-Connes-embeddable tracial GNS algebra, then a non-hyperlinear
countable group exists.  More precisely, choose an atom `H`, put

```text
Delta=N_Gamma(H),       K=Delta/H.                      (ANI2)
```

Then `Delta` has finite index in `Gamma`, `H` is normal in `Delta`, and

```text
L(K) is not Connes embeddable.                          (ANI3)
```

Thus `K` is non-hyperlinear.

Indeed, ergodicity and atomicity make `mu` the uniform measure on the finite
conjugacy orbit of `H`.  If `m=[Gamma:Delta]` and `r_1,...,r_m` are coset
representatives, the IRS character is

```text
chi_mu(g)=m^(-1) sum_i 1_(r_i^(-1) g r_i in H).         (ANI4)
```

Induce the regular representation of `K=Delta/H` from `Delta` to `Gamma`.
The usual finite-index cocycle matrix realizes it in

```text
M_m(L(K)),                                               (ANI5)
```

and its normalized matrix trace is exactly `(ANI4)`.  Consequently the GNS
von Neumann algebra of `chi_mu` embeds trace-preservingly in `M_m(L(K))`.
If `L(K)` were Connes embeddable, so would its matrix amplification and every
tracial von Neumann subalgebra, contradicting the hypothesis on `chi_mu`.

Applied to Manzoor's ergodic non-co-hyperlinear IRS, this gives a sharp
dichotomy:

```text
either its law is nonatomic,
or a non-hyperlinear group already exists.              (ANI6)
```

This isolates a real countable-group compiler that is stronger than the
normal-Dirac special case.  An atom need not be normal in `Gamma`; passing to
its finite-index normalizer is exactly what converts the finite conjugacy
orbit character into a canonical quotient group factor.

### Exact scope

Existence of an atomic non-co-hyperlinear IRS is in fact equivalent to
existence of a non-hyperlinear group.  The forward implication is the theorem
above.  Conversely, if `K` is a finitely generated non-hyperlinear group and
`F_r -> K` is a free presentation with kernel `N`, then the Dirac IRS
`delta_N` is atomic and its character is the pullback of the regular character
of `K`; its GNS algebra is `L(K)` and is non-CE.  Thus atomicity is a clean
terminal test on the Manzoor witness, not an independently easier existence
hypothesis.
