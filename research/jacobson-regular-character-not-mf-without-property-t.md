---
rg: 2
id: jacobson-regular-character-not-mf-without-property-t
kind: claim
title: Exclude the regular character of EL_5 of the binary Jacobson ring from the MF characters without property T
distinct_from:
  property-t-free-jacobson-head-collapse: that must kill the head in every norm-corona representation of EL_5(J); this must exclude only the models whose traces tend to the regular character, a strictly smaller class, and it is implied by that claim.
  leavitt-regular-character-not-mf-without-property-t: that excludes the regular character of EL_n(R) for the Leavitt ring R; this excludes it for the Jacobson subgroup EL_5(J), which embeds faithfully in EL_n(R) for n>=5, so this claim implies that one, and this one also closes the Steinberg goal.
  leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity: that equates CE characters of EL_n(J) with hyperlinearity; this asks for the operator-norm (MF) exclusion of one named trace and is implied by non-hyperlinearity of EL_5(J).
---

**OPEN.**  Let `J=F_2<S,T | TS=1>` and `E=EL_5(J)`.  Prove, using no
property `(T)`, Kazhdan projection, spectral-gap transport, or theorem whose
proof supplies such input, that there is **no** sequence of maps
`sigma_k:E->U(d_k)` with

```text
||sigma_k(gh)-sigma_k(g)sigma_k(h)|| -> 0,        tr sigma_k(g) -> 0   (g!=1).     (H1)
```

Here the first norm is the operator norm.

**Why it matters.**  By
`leavitt-mf-survivor-yields-jacobson-regular-character`, (H1) gives
`Rad_MF(St_20(L_(F_2)(1,2)))=St_20(L_(F_2)(1,2))`.  It also gives the regular
hole `leavitt-regular-character-not-mf-without-property-t` for `n>=5`.  It is
implied by `property-t-free-jacobson-head-collapse`, and also by
non-hyperlinearity of `EL_5(J)`.

**It can fail.**  It fails exactly when `EL_5(J)` admits regular-trace
operator-norm microstates.  In that case the whole Jacobson lane is dead,
because such a model retains the head.  The unrestricted statement (with
Kazhdan input) is true: `binary-jacobson-steinberg-head-root-is-mf-invisible`
kills every such model.  So (H1) is a provenance hole, not a truth-value
question.

**Structure the refutation may use.**
* By Kazhdan's uniform stability of finite groups, `sigma_k` is near a
  genuine representation on each finite window `F <= L`.  That
  representation's character tends to `delta_e^F`, so its isotypic
  multiplicities are asymptotically regular.  There are no low-multiplicity
  or rectangular isotypic escapes on the finitary kernel.
* Every element outside `L` has trace tending to `0` (Corollary B of
  `jacobson-el-characters-are-symbol-or-finitary-extensions` is automatic
  here).
* The one-sided relation `TS=1` must be used exactly.  The mirror LEF group
  of `jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group` has
  regular-trace LEF models, and it maps onto `E` with locally finite simple
  kernel `L_-`.  So an argument that never sees the quotient by `L_-`
  refutes a true statement.

## Attempts

- **2026-09-18, tensor saturation of the transport's spectral input
  (swarm-0917-w9-w9-ptl-break, stability-approximation).**  The attempt
  asked whether the Kesten gap `(MSG)` that the manuscript transport
  needs in the adjoint corona of a regular-trace model could be proved
  model-generically without `(T)`.  It cannot, except as a relative
  `(tau)` theorem.  `delta-e-adjoint-msg-is-fd-uniform-gap` shows the
  following.
  - Once one model `sigma` as in (H1) exists, `sigma (+) (sigma tensor U)`
    is again an (H1) model for every operator-norm model `U` of `E`.
  - Its adjoint corona contains `[U]` as an exact, normalized-rank-zero
    reducing corner.
  - So proving `(MSG)` on `L` for all (H1) models is equivalent to proving
    `(exists (H1) model) => T_MF(E,L)`.
  - That forces a uniform spectral gap for `L` on every finite-dimensional
    unitary representation of `E`. It includes `(tau)` for the image of
    `L` in the congruence quotients of `SL_5(F_2[z^(+-1)])`.

  Status: obstruction ESTABLISHED; this hole stays OPEN.  The only
  spectral arguments left are model-specific ones that use a property
  destroyed by adding a rank-zero tensor block (the tracial rung).
