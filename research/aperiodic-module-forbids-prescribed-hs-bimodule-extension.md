---
rg: 2
id: aperiodic-module-forbids-prescribed-hs-bimodule-extension
kind: claim
title: Aperiodicity forbids the prescribed finite-dimensional covariance bimodule extension
distinct_from:
  relative-kazhdan-bimodule-requires-whole-module-covariance: that computes the mixed-relator circularity of the canonical free-product action; this proves that even an arbitrary exact extension with the prescribed module restriction is impossible on a nontrivial finite-dimensional aperiodic module.
  semidirect-bad-orbit-needs-zero-trace-support: that constrains the restriction of a tracial state to a finite semidirect product; this is a representation-theoretic obstruction for the left-right Hilbert--Schmidt module action over an infinite aperiodic character actor.
  simple-t-augmentation-module-is-aperiodic: that proves the orbit hypothesis for the augmentation module; this consumes that hypothesis to rule out the proposed corrected bimodule.
---

Let an infinite group `A` act on an elementary abelian two-group `M`, and
assume that every nontrivial character in `widehat(M)` has infinite
`A`-orbit.  Let

```text
rho:M -> U(d)
```

be a finite-dimensional representation.  For `s in A`, define a unitary
representation of `M` on the Hilbert--Schmidt space `HS_d` by

```text
Sigma_s(m)X=rho(s m) X rho(m)^*.                         (APH1)
```

If `Sigma_s` is the restriction of a unitary representation of the
semidirect product `M rtimes A`, then

```text
rho(s m)=rho(m)                 for every m in M.        (APH2)
```

Consequently, if such an extension exists for every `s` in a generating set
of `A`, then `rho` is trivial.

## Proof

Because `M` has exponent two, every irreducible representation of `M` is a
sign character.  The finite-dimensional representation `Sigma_s` therefore
has a finite spectral support

```text
Supp(Sigma_s) subset widehat(M).                         (APH3)
```

Restriction of a representation of `M rtimes A` to the normal subgroup `M`
has `A`-invariant character multiplicities: conjugation by the operator
representing `a in A` carries the `chi`-weight space to the `a chi`-weight
space.  Hence `(APH3)` is a finite `A`-invariant set.  By the aperiodicity
hypothesis it is contained in the trivial character.  Thus

```text
Sigma_s(m)=I_(HS_d)              for every m in M.       (APH4)
```

Apply `(APH4)` to `X=I_d` in `(APH1)`.  This gives

```text
rho(s m)rho(m)^*=I_d,
```

which is `(APH2)`.

Now suppose `(APH2)` holds for every generator `s` of `A`.  Diagonalize the
commuting involutions `rho(M)`.  Every character `chi` in the spectral
support of `rho` satisfies

```text
chi(s m)=chi(m)
```

for every generator `s` and every `m`; hence `chi` is `A`-fixed.  The orbit
hypothesis forces `chi` to be trivial, so `rho(m)=I_d` for every `m`.

## Application to the proposed correction

For the augmentation host of
`simple-t-augmentation-module-is-aperiodic`, the exact restriction demanded
by `lamp-coupled-relative-bimodule-correction` is precisely `(APH1)`.  The
argument above does not depend on how the actor operators are corrected and
does not use their desired Kazhdan-set displacement bound.  Merely asking for
an exact semidirect-product extension for every actor generator already
forces the rounded module representation to be trivial.  It therefore
cannot preserve a visible seed lamp.

The relative-Kazhdan route cannot be repaired by replacing the canonical
free-product bimodule with an arbitrary representation having the same
module restriction.  A viable replacement must relax that restriction,
leave finite dimension, or use a different positive-definite kernel whose
finite spectral support is not required to be `A`-invariant.

