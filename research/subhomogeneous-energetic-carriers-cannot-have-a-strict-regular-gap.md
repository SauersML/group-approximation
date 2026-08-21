---
rg: 2
id: subhomogeneous-energetic-carriers-cannot-have-a-strict-regular-gap
kind: claim
title: A uniformly subhomogeneous energetic carrier cannot separate the regular trace from finite-dimensional traces
distinct_from:
  cyclic-carrier-energy-stability: that asks for equality of one support functional on CE and finite-dimensional traces together with a strict regular gap; this proves that obtaining the equality from subhomogeneity of the energetic carrier automatically destroys the strict gap.
  finite-normalizer-star-no-go: that computes one conditional Plancherel moment for a marked binary swap star; this applies to every positive energy in a subhomogeneous central packet sector and also to a finite orbit of noncentral packet corners.
  finite-selector-gadget-induction-barrier: that shows every compatible selector character occurs in some representation of a finite overgroup; this uses trace disintegration and finite Morita equivalence, with no abelian selector hypothesis.
  low-dimensional-hyperoctahedral-packet-groupifies-any-predicate: that classifies marked irreducibles below a chosen dimension cutoff; this rules out using a uniform cutoff on the whole energetic carrier to obtain the strict regular-versus-finite ceiling needed by reverse Kleene.
---

Let `A` be a unital C-star algebra, let `q` be a central projection, and let
`a in (qAq)_+`.  Suppose `qAq` is `D`-subhomogeneous: every irreducible
representation has dimension at most `D`.  If

```text
beta_fd(A,a)=sup{tr_dim(pi)(pi(a)):
                 pi is a finite-dimensional unital representation of A},
```

then every tracial state `tau` on `A` satisfies

```text
tau(a)<=beta_fd(A,a).                                    (SEC1)
```

In particular, for a discrete group `G`, if a positive group-algebra energy
is supported on such a central carrier in `C*(G)`, then

```text
E_reg<=beta_fd.                                          (SEC2)
```

Thus uniform subhomogeneity proves the one-functional upper-semicontinuity
part of `cyclic-carrier-energy-stability` only by making its required strict
inequality impossible.

The same conclusion holds for a noncentral finite-packet projection `p` if
its normalizer orbit consists of `m` mutually orthogonal projections
`p_1=p,...,p_m` with central sum `q`, and `p` is full in `qAq`.  If `pAp` is
`D`-subhomogeneous, finite Morita induction makes `qAq`
`mD`-subhomogeneous, so `(SEC1)--(SEC2)` apply to every positive energy in
the orbit carrier.

Consequently a reverse-Kleene bounded energetic-witness extractor cannot be
obtained by forcing the whole canonical finite-packet/normalizer carrier to
be uniformly subhomogeneous.  Any viable bounded extractor must be
conditional on the canonical microstate in a way not inherited by all
representations of the carrier, or must use a non-functorial matrix-only
selection rather than a subhomogeneous C-star corner.

