---
rg: 2
id: nonhyperlinear-via-parity-compressor
kind: route
title: Turn the parity compressor's half-trace excess projection into a finitely presented obstruction
target: non-hyperlinear-group
requires:
  - toeplitz-parity-compressor-candidate
  - parity-compressor-hs-return
---

By `toeplitz-parity-compressor-candidate`, `J` is nontrivial in `H_T`.  If
`H_T` were hyperlinear, its canonical trace would embed faithfully in a
tracial matrix ultraproduct, giving `pi(J)!=1` (indeed `tau(pi(J))=0`).  This
contradicts `parity-compressor-hs-return`.  Hence that endpoint makes `H_T`
nonhyperlinear.

The group `H_T` is finitely generated and recursively presented.  Higman's
embedding theorem places it in a finitely presented group `G`.  Hyperlinearity
passes to subgroups, so hyperlinearity of `G` would imply hyperlinearity of
`H_T`.  Therefore `G` is a finitely presented nonhyperlinear group.

Only the open HS-return claim is missing.  The exact-representation theorem,
the Toeplitz realization, the half-trace carrier calculation, and the final
Higman reduction are already unconditional.

