---
rg: 2
id: subgroup-dehn-function-is-the-hyperlinearity-modulus
kind: claim
title: The Dehn function of a subgroup in a finitely presented host is the modulus at which almost representations descend
artifacts:
  - research/artifacts/two-paper-ingestion-2026-08-19.md
distinct_from:
  bounded-overlap-syndrome-energy-accounting: that converts local syndrome charges with bounded overlap into a global energy bound inside one microstate; this converts relator defect of a host into relation defect of a subgroup along a van Kampen filling, and its constant is a Dehn function.
  quantitative-higman-embedding-with-dehn-control: that is the imported embedding theorem supplying a host with a small relative Dehn function; this is the elementary lemma explaining why a small relative Dehn function is worth having.
  hyperlinear-quotient-permanence-equivalence: that concerns permanence of hyperlinearity under quotients; this is subgroup heredity made quantitative and says nothing about quotients.
---

Let `H = <A | R>` be a finitely presented group, let `G = <B> <= H` be finitely
generated with each `b in B` a fixed word `w_b` over `A`, and let
`delta_(G,H)` be the Dehn function of `G` in `H`.  Let `d` be any dimension and
let `pi : F(A) -> U(d)` be the homomorphism determined by a unitary `A`-tuple,
with normalized Hilbert--Schmidt relator defect

```text
max_(r in R) ||pi(r) - 1||_2 <= delta.
```

Define the induced `B`-tuple by `pi_G(b) = pi(w_b)`.  Then for every word `w`
over `B u B^-1` with `|w|_B <= n` and `w =_G 1`,

```text
||pi_G(w) - 1||_2 <= delta_(G,H)(n) . delta.                      (SDM1)
```

**(SDM2) Effective subgroup heredity.**  Consequently a hyperlinear `H`
supplies, for each fixed `n`, unitary `B`-tuples satisfying every relation of
`G` of length at most `n` to within `delta_(G,H)(n) . delta` with `delta`
arbitrarily small, and a diagonal choice recovers hyperlinearity of `G`.  The
qualitative fact that subgroups of hyperlinear groups are hyperlinear is
therefore quantitative, with `delta_(G,H)` as its explicit modulus.

**(SDM3) Certificate transfer.**  Suppose `z` is a word over `B` with `z != 1`
in `G`, and suppose an *effective* non-hyperlinearity certificate for `G` is
available at scale `(n, epsilon, alpha)`: every unitary `B`-tuple satisfying
all relations of `G` of length at most `n` to within `epsilon` has
`||z - 1||_2 < alpha`.  Then every unitary `A`-tuple with relator defect

```text
delta < epsilon / delta_(G,H)(n)
```

has `||pi(w_z) - 1||_2 < alpha`, while `w_z != 1` in `H`.  So the certificate
transfers to the finitely presented host with its scale divided by
`delta_(G,H)(n)`, and by nothing else.

This is why the *relative* Dehn function is the quantity to minimize when
choosing a finitely presented host: it is the exact exchange rate between the
host's relator budget and the subgroup's relation budget.  Nothing here needs
the embedding to be undistorted; distortion controls the relation between
`|w|_A` and `|w|_B`, which enters only if one wants to compare the two word
metrics as well.

Golan's theorem that every copy of Thompson's `F` in `F` is undistorted
([arXiv:2608.17193](https://arxiv.org/abs/2608.17193)) does not change this
gate.  It controls the comparison of word metrics, whereas `(SDM1)--(SDM3)`
need relative filling area to convert host relator defect into subgroup
relation defect.  It is therefore useful corroboration for the metric side,
not a replacement for `quantitative-higman-embedding-with-dehn-control`.
