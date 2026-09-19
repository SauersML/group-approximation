---
rg: 2
id: fm-stone-lamp-corners-are-singular
kind: claim
title: Feldman--Moore Cartans cannot be recovered from additive Stone lamps in any nonzero corner
distinct_from:
  stone-multiplicative-locus-is-haar-null-in-additive-dual: that computes the null Stone locus and excludes central or reducing spectral sectors in an arbitrary group algebra; this proves that unitarity of a literal compressed-lamp Cartan map automatically forces reduction, and applies it actor-independently to the whole Feldman--Moore compiler.
  stone-additive-semidir-product-loses-manzoor-measure: that exhibits a single wrong-weight event for the native Manzoor actor; this rules out every countable graphing actor and every nonzero, initially noncentral, corner at once.
  full-group-subgroup-trace-generation-dichotomy: that concerns canonical full-group unitaries and their fixed-point trace; this concerns the Cartan event algebra and the singular Stone measure before any normalizer is mapped.
---

**ESTABLISHED.**  Let `R` be a countable pmp equivalence relation on a
diffuse standard probability space `(X,mu)`, let `D=L^infinity(X)`, and let
`B` be a countable atomless Boolean algebra of measurable sets which generates
`D` modulo null sets.  Let

```text
L=(B,symmetric_difference),       K=dual(L),
```

and let any countable group `Lambda` act on `B` by Boolean automorphisms.  Its
dual action on `K` is algebraic and Haar preserving.  Put

```text
M=L^infinity(K,Haar) rtimes Lambda,
```

and write `u_a in L(L) subset M` for the additive lamp indexed by `a in B`.

There is no nonzero projection `q in M` and no normal trace-preserving
star-homomorphism

```text
Phi:D -> (qMq, tau(q)^(-1)tau)
```

such that

```text
Phi(1-2 1_a)=q u_a q                  for every a in B.   (FSC1)
```

Consequently no trace-preserving embedding of `L(R)` into `qMq` can map its
Feldman--Moore Cartan through the literal additive Stone lamps in `(FSC1)`.
This remains false if `Lambda` is a countable full-group graphing of `R`, an
arbitrary enlargement of such a graphing, or if the corner `q` is not assumed
central or reducing in advance.

Indeed, each source sign `1-2 1_a` is a unitary.  If `q u_a q` is a unitary
of `qMq`, the two compression defect identities imply

```text
(1-q)u_aq=0=q u_a(1-q),
```

so `q` commutes with every `u_a`, hence with `L^infinity(K)`.  The spectral
law of the compressed lamp representation with normalized corner trace is
therefore absolutely continuous with respect to Haar measure on `K`; its
density is

```text
h=E_(L^infinity(K))(q)/tau(q).                          (FSC2)
```

On the other hand, the joint spectral law of the source signs is the Stone
probability measure of `(B,mu)`.  It is supported on the Boolean-
multiplicative locus

```text
S={chi in K: chi comes from an ultrafilter of B}.        (FSC3)
```

For a finite Boolean subalgebra with `n` atoms, Haar gives its ultrafilter
restrictions mass `n/2^n`; atomlessness supplies arbitrarily large `n`, so
`Haar(S)=0`.  Trace preservation in `(FSC1)` equates every Fourier coefficient
of the law in `(FSC2)` with the Stone law in `(FSC3)`.  Fourier uniqueness on
the compact group `K` would make these two probability measures equal,
contradicting absolute continuity versus concentration on the Haar-null set
`S`.

This closes the canonical Feldman--Moore/Boolean-lamp route, not the full
algebraic-envelope problem.  An exotic non-Cartan embedding into an algebraic
crossed product, or a nonlinear image of the Cartan signs involving genuine
actor-grade sums rather than compressed literal lamps, is outside `(FSC1)`.

DERIVATION
fm-stone-lamp-corner-singularity-proof
