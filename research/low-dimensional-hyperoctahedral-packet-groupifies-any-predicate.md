---
rg: 2
id: low-dimensional-hyperoctahedral-packet-groupifies-any-predicate
kind: claim
title: One hyperoctahedral packet enforces any Boolean predicate below a quadratic dimension threshold
distinct_from:
  all-bcs-contexts-share-one-hyperoctahedral-signed-type: that selects one tautological signed block by a Hecke idempotent; this proves that every sufficiently low-dimensional marked irreducible already has the desired joint spectrum.
  finite-selector-gadget-induction-barrier: that forbids deleting arbitrary selector characters from all representations of a finite overgroup; this retains other characters in higher-dimensional irreducibles and uses a dimension cutoff.
  marked-clifford-table-exponential-dimension: that forces dimension from independent Pauli pairs but carries no arbitrary Boolean selector predicate; this simultaneously supplies a predicate spectrum and a linear marked-dimension floor.
---

Let `R` be any nonempty subset of `{+1,-1}^k`.  Choose an even integer `L`
and put

```text
m=L|R|,                    m>=8,
W_m=(C_2)^m semidirect S_m.                              (HLP1)
```

Label the `m` sign coordinates by `L` copies of every `a in R`.  Let `d_x`
be the diagonal sign element whose coordinate labelled by `a` equals `a_x`,
and let

```text
J=(-1,...,-1) in (C_2)^m.                               (HLP2)
```

Then every irreducible complex representation `pi` of `W_m` satisfying

```text
pi(J)=-I,                  dim(pi)<m(m-2)               (HLP3)
```

has joint spectrum of `pi(d_1),...,pi(d_k)` contained in `R`.  More
precisely, `dim(pi)=m` and the joint spectrum is exactly the multiset
consisting of `L` copies of `R`.

Consequently every representation of total dimension below `m(m-2)` has the
predicate `R` exactly on its whole marked `J=-1` sector.  In particular, no
representation of dimension less than `m` has a nonzero marked sector.

The construction is effective and uses only the multiplication table of one
finite hyperoctahedral group.  It does not contradict finite-selector
induction: marked irreducibles of dimension at least `m(m-2)` may carry other
diagonal spectra.
