---
rg: 2
id: finite-dimensional-kazhdan-fixed-algebra-transport
kind: claim
title: Finite-dimensional invariant algebras have identical parent and compressed fixed points
distinct_from:
  finite-noncommutative-packet-compression-collapse: That concerns a finite group packet; this permits any finite-dimensional invariant C-star subalgebra and replaces the weighted cocycle by exact covariance and the ordinary Kazhdan gap.
artifacts:
  - research/artifacts/finite-block-perfect-mf-radicals.md
---

Let G be countable, L<=G have property (T), tLt^-1<=L, and let
rho:G->U(Q) be a norm matrix corona homomorphism. For every finite-dimensional
unital C-star subalgebra A<=Q normalized by rho(L),

    A^(Ad rho(tLt^-1)) = A^(Ad rho(L)).

In particular a finite subgroup normalized by L cannot retain an element
fixed only by the compressed copy. Sections 1--2 of the artifact give the
complete written proof, including covariance correction before normalization
and the case of nonfaithful coordinate lifts. No new Lean verification is
claimed.
