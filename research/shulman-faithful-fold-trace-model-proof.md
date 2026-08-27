---
rg: 2
id: shulman-faithful-fold-trace-model-proof
kind: route
title: Combine residual finite regular fold blocks with one faithful Shulman block
target: shulman-presentation-double-has-a-faithful-fold-trace-model
requires:
  - shulman-amalgam-mf-criterion
  - virtually-free-full-algebras-are-rfd
  - faithful-mf-models-realize-all-mf-traces
  - leavitt-presentation-double-fd-radical-is-fold-kernel
---

Enumerate the nonidentity elements of the finitely generated free group `F`.
Residual finiteness gives finite quotients `q_n:F->A_n` such that every fixed
nonidentity element has nontrivial image for all sufficiently large `n`
(take the product of the first `n` separating quotients).  The normalized
characters of the regular representations `lambda_(A_n) q_n` therefore
converge to the canonical character of `F`.

Their integrated representations of `C*(F)`, composed with `C*(p)`, are
exact star representations of `B` whose traces converge on the group ring to
`tau_fold`.  Contractivity and density extend the convergence to all of
`B`, proving that `(SFT1)` is an MF trace.

The full vertex algebra `C*(F)` is RFD and hence MF.  Shulman's symmetric
case in `shulman-amalgam-mf-criterion`, together with
`C*(P)=C*(F) *_(C*(K)) C*(F)`, therefore supplies an asymptotically
isometric MF model of the full algebra `B`.  Apply
`faithful-mf-models-realize-all-mf-traces` to that faithful model and the
folded trace coordinates above.  This gives the claimed faithful coordinate
model inducing `tau_fold`.

Let `s` interchange the two vertex copies.  Direct sums preserve all MF
defects and asymptotic isometry, so `(SFT1*)` is another faithful model.  A
literal block flip gives `(SFT1**)`.  The identity `p s=p` gives
`tau_fold s=tau_fold`, and hence the trace of `(SFT1*)` still converges to
`tau_fold`.

Since `p i_0=p i_1=id_F`, restricting `(SFT1)` to either vertex gives
`tau_F`, which is `(SFT1***)`.

Finally, `C*(p)(u_w)=1` for `w in ker(p)`, so every folded trace coordinate
already makes `(u_w-1)^*(u_w-1)` zero.  This proves `(SFT2)` and the stated
trace-selection no-go.
