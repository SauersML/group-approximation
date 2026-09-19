---
rg: 2
id: commutant-density-trace-blind
kind: claim
title: The normalized commutant density is a character invariant, and vanishes on regular-character models
distinct_from:
  invariant-size-collapse: That claim is the abstract two-hypothesis lemma — a conjugation-invariant size distinguishing proper inclusions forces collapse — and records that the II_1 trace fails the second hypothesis; this one identifies the concrete candidate size in the tracial setting, gives its closed form in terms of the character, and shows it is identically zero rather than merely refinement-blind.
  commutant-no-growth: That claim is the exact finite-dimensional dimension count; this one shows that count has no informative normalized shadow.
  finite-quotient-blindness: That claim says finite quotients normalize the image of the subgroup, destroying the compression data before any construction; this one is about the normalized dimension invariant of matrix microstates, which need not be quotients at all.
  kazhdan-asymptotic-commutant-transport: That claim transports asymptotic commutants in operator norm and kills the wall in the norm-microstate sector; this one is a negative statement about a proposed normalized-Hilbert--Schmidt counting method.
artifacts:
  - notes/TRUE_WALL_ENERGY_AND_COMMUTANT_DENSITY.md
---

Let `Gamma` be finitely generated, infinite, with property `(T)`, and let
`(mu_j)` be a Kazhdan sequence.  For `rho:Gamma->U(d)` put

```text
D_j(rho)=sum_gamma mu_j(gamma)|tr_d(rho(gamma))|^2.
```

For a genuine representation `lim_j D_j(rho)=dim(rho(Gamma)')/d^2`, because
`Tr(Ad rho(gamma))=|Tr rho(gamma)|^2`.  For normalized-Hilbert--Schmidt
asymptotic representations the densities of `Gamma` and of
`t Gamma t^(-1)` differ by at most twice the multiplicative defect on the
window, hence agree in the limit; and if the limit character is supported at
the identity — the canonical trace of `Cl(X) crossed_product G`, of `L(W)`,
or of any free-lamp model over the regular character — the density is `0`,
since `mu_j(1)->0` for infinite `Gamma`.

So the isotropy/orbit counting behind Kun--Thom Theorem 4.1 and its
exact-representation form `commutant-no-growth` degenerate in the tracial
ultraproduct to `0=0`.  The surviving II_1 substitute is the Pimsner--Popa
index, which is not normalized.

Two qualifications, since this is a negative statement about a method and
should be read weakly.  The conjugation-invariance half is unconditional;
the **vanishing half is conditional** on the character being supported at
the identity, which is why the title says so.  And the limit computed is the
**iterated** one, `lim_j lim_n`, with no uniformity in `j` claimed: enough to
deny the counting method its comparison, not enough to use the density as an
invariant in its own right.
