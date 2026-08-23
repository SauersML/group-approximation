---
rg: 2
id: threshold-free-mf-compiler-equivalence
kind: claim
title: The bare threshold-free MF compiler is equivalent to a marked non-MF seed
artifacts:
  - research/artifacts/seeded-self-aware-mf-switch-2026-08-23.md
distinct_from:
  threshold-free-reverse-kleene-mf-higman: that proves compiler implies a finitely presented non-MF group; this adds the converse and identifies the exact logical strength of the compiler interface.
  authenticated-opnorm-challenge-compiler: that originally proposed one support-profile implementation; this classifies the extensional TFM1--TFM2 specification independently of any implementation.
---

The following are equivalent.

1. There is a finitely presented group `H` with a word
   `1!=z in Res_MF(H)`.
2. There is a total computable compiler to uniformly recursively presented
   marked groups satisfying the threshold-free clauses

   ```text
   e halts     => w_e!=1,
   e nonhalts  => w_e in Res_MF(Gamma_e).
   ```

The forward implication is the one-generator proof-triggered switch. The
reverse implication is reverse Kleene followed by effective Higman; the
fixed-point word remains both nontrivial and MF-invisible under the embedding.
Hence the bare compiler interface, by itself, cannot certify a seed-free or
independent source of non-MF-ness.
