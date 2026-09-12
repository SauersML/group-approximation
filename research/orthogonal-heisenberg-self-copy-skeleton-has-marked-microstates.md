---
rg: 2
id: orthogonal-heisenberg-self-copy-skeleton-has-marked-microstates
kind: claim
title: The full orthogonal Heisenberg self-copy skeleton has marked finite-window microstates
distinct_from:
  orthogonal-root-self-copy-is-mf-compatible: that uses two block copies inside the finitary elementary group but has no stable letters conjugating the whole parent onto each child; this includes both global branch conjugacies and keeps their common central mark in one coherent microstate sequence.
  bare-self-copy-mf-calibration: that treats one dyadic compression with a commutant mark; this treats two commuting Heisenberg branches which generate the parent and share the marked center.
  leavitt-character-mass-escapes-to-finer-characters: that explains the marginal loophole abstractly; this realizes the loophole by one pair of coordinate-permutation implementers coherent on every fixed window.
---

**ESTABLISHED CALIBRATION.** Let

```text
V=directSum_(n>=0) F_p e_n
```

with its coordinate pairing, and let `H(V)` be the Heisenberg group generated
by `X(v),Y(w),Z`, with

```text
[X(v),Y(w)]=Z^(<v,w>).
```

Define two injective endomorphisms by the orthogonal coordinate embeddings

```text
f_0(e_n)=e_(2n),       f_1(e_n)=e_(2n+1),
alpha_i(X(v))=X(f_i v),
alpha_i(Y(w))=Y(f_i w),
alpha_i(Z)=Z.                                           (OHS1)
```

Their images commute modulo their common center, have intersection exactly
`<Z>`, and generate `H(V)`.  Form the multiple ascending HNN extension

```text
Gamma=<H(V),u_0,u_1 |
       u_i h u_i^(-1)=alpha_i(h), h in H(V), i=0,1>.    (OHS2)
```

Then `Z` is nontrivial in `Gamma`, and `(Gamma,Z)` has a presentation
microstate sequence in which `Z` acts as one fixed nontrivial scalar
`zeta I`.  More precisely, every finite collection of relations from
`(OHS2)` has an exact finite-dimensional realization with this marked scalar.

At stage `M`, use the Schrödinger representation of the finite coordinate
Heisenberg group on `l2(F_p^M)`.  For a prescribed finite window supported on
the first `L` coordinates, with `2L<=M`, choose permutations
`sigma_(i,M)` of the `M` coordinates which agree with `f_i` on those first
`L` coordinates.  Their permutation unitaries implement `(OHS1)` exactly on
the whole prescribed window and fix `Z=zeta I`.  Enlarging `L` along a
diagonal sequence gives the claimed microstates.

Thus even the following data together do not imply a coherent Leavitt
decoder:

1. one common positive-density marked central carrier;
2. two commuting child Heisenberg copies generating the parent;
3. one globally reused stable letter conjugating the parent to each child;
4. all transverse Heisenberg shears on every fixed window; and
5. exact compatibility as the finite window grows.

The successful decoder must use relations outside this orthogonal
self-copy skeleton.  Concretely, it must couple the exponentially many
polarized characters through a same-reservoir coefficient return that the
finite coordinate permutations cannot satisfy.
