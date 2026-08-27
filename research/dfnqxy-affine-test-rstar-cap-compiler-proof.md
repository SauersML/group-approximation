---
rg: 2
id: dfnqxy-affine-test-rstar-cap-compiler-proof
kind: route
title: Compile the affine Hadamard tests through one pinned R-star cap
target: dfnqxy-nonverify-rows-have-cap-safe-rstar-pp-compilers
requires:
  - dfnqxy-answer-reduction-does-not-preserve-affine-safe-support
  - rstar-cap-support-is-one-character-row
  - culf-mastel-rstar-reduction-is-support-blind
---

Use the primary-source test audit to discard `Verify`: every remaining
predicate is a conjunction of affine Boolean equations.  Pin private bits
`z=0,o=1` by `R_*(z,o,o,o)`.  Compile a partial xor
`w=u+v` by `R_*(u,v,w,o)` and equality by `R_*(u,v,z,o)`.  Chaining these
rows presents every affine source relation exactly.  Every row has last
coordinate `o=1`, hence lies in one fixed maximal Fano cap.  On an exact
commuting source context the auxiliaries are spectral products of its old
variables, so the lift preserves the original CE algebra and all visible
overlaps.  Private auxiliary sets and constant answer size let this explicit
choice replace the arbitrary NP gadget without changing the published
constant-soundness reduction.
