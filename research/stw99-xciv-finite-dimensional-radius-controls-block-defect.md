---
rg: 2
id: stw99-xciv-finite-dimensional-radius-controls-block-defect
kind: claim
title: Finite-dimensional norm radius bounds the fixed-block centralization defect
distinct_from:
  stw99-xciv-norm-matrix-tower-has-zstable-hull: that theorem assumes one coherent infinite tower with growing Bratteli multiplicities and constructs a Z-stable hull; this theorem treats a single finite test, needs no coherence or multiplicity, and uses the ambient II1 relative commutant.
  stw99-xciv-commuting-car-seed-has-zstable-hull: that theorem assumes an exact CAR copy in the commutant of an entire separable seed; this theorem only centralizes one finite tuple and obtains its block from the commutant of a nearby finite-dimensional algebra.
  stw99-xciv-two-norm-centrality-does-not-control-norm-centrality: that theorem shows tracial approximation cannot select norm-central representatives; this theorem assumes and quantitatively exploits actual operator-norm proximity to finite-dimensional subalgebras.
  stw99-xciv-single-prime-block-centrality-is-exact: that theorem identifies the local fixed-block condition equivalent to the root; this theorem proves that condition for a concrete class of finite tests and quantifies what any negative certificate must avoid.
artifacts:
  - research/artifacts/stw99-xciv-local-fd-radius-audit-2026-08-30.md
---

Fix `D=I_(2,3)` and a finite self-adjoint contractive generating set `H`.
For a finite `F subset R`, define its finite-dimensional norm radius

```text
alpha_R(F)=inf_E max_(a in F) dist(a,E),                 (1)
```

where `E` ranges over unital finite-dimensional C*-subalgebras of `R`.
Define the fixed-block commutator defect

```text
gamma_D(F)=inf_psi max_(a in F,h in H)||[a,psi(h)]||,    (2)
```

where `psi:D->R` ranges over unital homomorphisms.  Then

```text
gamma_D(F)<=2 alpha_R(F).                               (3)
```

Consequently every finite `F` with `alpha_R(F)=0` admits arbitrarily
operator-norm-central unital copies of the fixed block `I_(2,3)`.

In particular `(3)` applies with zero right-hand side when `F` is contained
in a finite type-I von Neumann subalgebra of uniformly bounded degree.  This
includes every finite family of commuting normal elements of `R`: their
joint abelian von Neumann algebra admits uniform finite-range step-function
approximants.

Conversely, any finite norm-gap certificate

```text
gamma_D(F)>=delta>0
```

for a negative answer to XCIV must satisfy

```text
alpha_R(F)>=delta/2.                                   (4)
```

Thus a negative witness cannot be norm-locally finite-dimensional.  The
hyperfinite `2`-norm approximation of `F` gives no information about `(1)`
and does not contradict `(4)`.

This is a local finite-test theorem; it does not assert that an arbitrary
separable type-I seed has a single Z-stable hull.
