---
rg: 2
id: torsion-free-lef-kazhdan-non-rf-seed-proof
kind: route
title: Use a characteristic-zero one-sided centre, periodic finite windows, and a torsion-free finite-index preimage
target: torsion-free-lef-kazhdan-non-rf-seed
requires: []
artifacts:
  - research/artifacts/torsion-free-lef-kazhdan-seed-2026-08-26.md
---

## Property (T)

Appendix A of Kida--Tucker-Drob, *Groups with infinite FC-center have the
Schmidt property* (arXiv:1901.08735), proves the parabolic argument over
`Z[t]`.  Its proof uses only the following inputs for the coefficient ring:

1. the elementary rank-three group over the finitely generated ring has
   property `(T)`;
2. its natural semidirect pair with `R^3` has relative property `(T)`; and
3. the top-right root lies in the commutator subgroup.

The same inputs hold for the finitely generated Laurent ring
`R=Z[t,t^(-1)]` by the universal-lattice property-`(T)` theorem of
Ershov--Jaikin-Zapirain and Kassabov's relative-`(T)` theorem.  Applying the
extension criterion twice gives property `(T)` for

```text
H/C ~= EL_3(R) semidirect (R^3 x R^3).
```

Since `C <= [H,H]`, the central-extension criterion used in the appendix
gives property `(T)` for `H`, and quotient permanence gives it for
`J=H/C_+`.

## LEF

Fix a finite multiplication window in `J`, choose Laurent-matrix
representatives, and let all coefficients and exponents occurring in the
window and its products be bounded by `B` and `N`.  Choose a prime `q` larger
than the coefficient bound and a period `M>6N`.  In the finite ring

```text
S=(Z/qZ)[xi,xi^(-1)]/(xi^M-1)
```

send `t^k` to `xi^k`.  In the central root of `H(S)`, kill the span `C_N` of
the residues `xi^k` with `0<=k<M/2`.  On exponents between `-2N` and `2N`,
the cyclic reduction has no wrap-around: a Laurent polynomial lies in
`Z[t]` exactly when its image lies in `C_N`.  Taking `q` larger if necessary
also prevents coefficient cancellation.  Thus the window and its product
table inject into the finite group `H(S)/C_N`.  This is the characteristic-
zero version of Thom's proof of Lemma 2.3 and proves that `J` is LEF.

## A nontrivial infinite-order finite-residual element

Let `delta` be conjugation by `diag(t,I_3,1)` on `H`.  On the centre it is
multiplication by `t`, so `delta(C_+) properSubset C_+`; it induces a
surjective noninjective endomorphism `alpha:J->J`.  The class of `t^(-1)` is
nontrivial, has infinite order because `R/C_+` is free abelian, and belongs
to `ker alpha`.

For a finite quotient `q:J->F`, all maps `q alpha^n` are onto `q(J)` and
their kernels have one fixed finite index.  The finitely generated group `J`
has only finitely many subgroups of that index, so two kernels repeat.
Surjectivity of the smaller power of `alpha` cancels it and yields

```text
ker q = ker(q alpha^d)
```

for some `d>0`.  Hence `ker alpha <= ker q`; in particular the displayed
central element lies in every finite quotient kernel.

## Remove torsion without removing the obstruction

The centre-free quotient `Gamma=H/C` is a finitely generated subgroup of a
general linear group over `Q(t)`.  Selberg's lemma supplies a torsion-free
finite-index subgroup.  Intersecting all subgroups of that same index gives
a characteristic torsion-free finite-index subgroup `Gamma_0`.  Let `K` be
the preimage of `Gamma_0` under `J->Gamma`.  Then

```text
1 -> C/C_+ -> K -> Gamma_0 -> 1
```

has torsion-free kernel and quotient, so `K` is torsion-free.  It is
finite-index in `J`, hence finitely generated and Kazhdan, and it is LEF as a
subgroup of `J`.

The central finite-residual element belongs to `K`.  If `N normal K` had
finite index and omitted it, then `N` has finite index in `J`; its core in
`J` also has finite index.  Centrality says every conjugate of `N` omits the
element, so the core omits it, contradicting finite-residual invisibility in
`J`.  Therefore `K` is non-residually-finite, completing the proof.

Finally LEF implies both soficity and operator-MF.  These implications are
formalized in `isSofic_of_isLEF` and `isOperatorMF_of_isLEF`; no additional
property of the construction is needed.
