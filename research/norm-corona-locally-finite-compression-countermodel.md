---
rg: 2
id: norm-corona-locally-finite-compression-countermodel
kind: claim
title: The norm corona hosts a locally finite compression whose defect survives
artifacts:
  - research/norm-corona-locally-finite-compression-countermodel-proof.md
  - notes/PROPERTY_T_FREE_MF_ATTEMPT_2026-08-26.md
distinct_from:
  uhf-cyclic-shift-has-strict-compressed-commutant: that isolates strict failure of relative-commutant normalization in the same tensor-tail geometry; this packages the compressor with a countable amenable group and exhibits an explicit nontrivial central defect surviving its tautological MF representation.
  trace-blindness-sharpness: that is a tracial Bernoulli-shift counterexample in a finite von Neumann setting; this is an operator-norm matrix-corona group with a strict one-sided compression.
  finite-infranormal-subgroup-is-normal: that forbids strict compression of a finite subgroup; this uses an infinite locally finite subgroup.
  one-variable-no-compressor: that excludes a strict compressor in one arithmetic model; this exhibits a strict compressor and an MF-visible defect.
---

Let

```text
Q=product_n M_(2^n)(C)/directSum_norm M_(2^n)(C).
```

There are a countable locally finite subgroup `L<=U(Q)`, a unitary `c`, and
an element `c'` such that, for `G=<L,c>`:

1. `cLc^(-1)<L` is a proper one-sided compression;
2. `c'` belongs to `G` and centralizes `L`;
3. `cc'c^(-1)` belongs to `L`, and for a suitable `l in L`,
   `[cc'c^(-1),l]=-1_Q`; in particular this nontrivial central defect is
   not killed by the tautological homomorphism `G->U(Q)`;
4. `c^(-1)(L' intersect Q)c<L' intersect Q`, and the same coordinate lift
   fails to preserve the Hilbert--Schmidt asymptotic commutant;
5. `G` is amenable, being a quotient of an ascending HNN extension of the
   locally finite group `L`.

Therefore the one-sided compression criterion used by the manuscript is
false if Property `(T)` of the compressed subgroup is replaced merely by
amenability or local finiteness.  A Property-`(T)`-free proof for the
binary-Leavitt group must consume additional coefficient-sensitive
relations; there is no generic corona compression lemma waiting to replace
Kazhdan transport.

This is an operator-norm statement.  No Property `(T)`, stability theorem,
or literature input is used.

DERIVATION
norm-corona-locally-finite-compression-countermodel-proof
