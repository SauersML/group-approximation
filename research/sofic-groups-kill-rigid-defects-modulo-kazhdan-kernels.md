---
rg: 2
id: sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels
kind: claim
title: Sofic groups kill rigid compression defects modulo normal Kazhdan subgroups
distinct_from:
  sofic-groups-kill-rigid-compression-defects: that is the established absolute criterion, which is the case M = 1 here; this allows a normal Kazhdan subgroup M inside the compressed group and asks the defect only to lie in M, which is what a hyperbolic host can still violate.
  rigid-compression-defect-normalization-dichotomy: that is the equivalence between absolute defect killing and centralizer normalization in ultraproducts; this is the relative criterion, whose ultraproduct form needs normalization only modulo the image of M.
  sofic-quotients-by-kazhdan-normal-subgroups-are-sofic: that is quotient permanence of soficity itself, which implies this; this asks only that the rigid-defect criterion hold for such quotients.
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

**OPEN.** Let `H` be a countable sofic group, let `M` be a normal subgroup of
`H` with property (T), and let `Gamma <= G <= H` be a rigid pair (both
Kazhdan, `Gamma` infranormal in `G`) with `M <= Gamma`. Then

```text
[g z g^-1, gamma] in M     for all g in G, gamma in Gamma, and z in H with [z, Gamma] <= M.
```

**Equivalent form.** Every quotient of a sofic group by a normal Kazhdan
subgroup has trivial rigid defect. This holds because rigid pairs of `H/M`
correspond to rigid pairs of `H` containing `M`:

- preimages of Kazhdan groups are Kazhdan, because `M` is Kazhdan;
- preimages of compressors compress the preimage;
- `z M` centralizes `Gamma/M` exactly when `[z, Gamma] <= M`.

The case `M = 1` is `sofic-groups-kill-rigid-compression-defects`.

**Win--win.** By `hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup`
there is a hyperbolic Kazhdan group whose relative defect modulo a Kazhdan
kernel is nontrivial. So this claim implies that some hyperbolic group is not
sofic (`nonsofic-hyperbolic-via-relative-rigid-defect`). Conversely, if every
hyperbolic group is sofic, the Leavitt cover
`hyperbolic-kazhdan-cover-of-leavitt-unit-group` refutes this claim.

## Attempts

- **Through quotient permanence.** `sofic-quotients-by-kazhdan-normal-subgroups-are-sofic`
  implies this claim at once, through the absolute criterion applied to `H/M`.
  That premise is open and at least as strong.
- **Normalize modulo `M` in the ultraproduct.** For a sofic representation
  `sigma` of `H`, Kun--Thom Theorem 4.1 applied to the pair containing `M` says
  `sigma(G)` normalizes `C(sigma(Gamma))`. An element `z` with
  `[z, Gamma] <= M` gives `sigma(z)`, which commutes with `sigma(Gamma)` only
  up to `sigma(M)`. To conclude, one would correct `sigma(z)` by a permutation
  `w` that preserves every block of the Kazhdan fixed-algebra partition of `M`
  (Kun--Thom Lemma 2.3) and makes `sigma(z) w` commute with `sigma(Gamma)`.
  That is a blockwise conjugacy problem for expander actions twisted by an
  `M`-valued cocycle, and no uniqueness theorem for it is available. **This is
  where it stops.**
- **Fixed algebras of the invariant factor.** Kun--Thom Theorem C applied to the
  pair containing `M` gives fixed-algebra rigidity on the `M`-invariant factor,
  where `H/M` acts. That factor action need not be free: in any finite-quotient
  model of the Leavitt cover, `R^x` acts on it trivially. So no Corollary D
  conclusion follows. Dead as stated.
- **Blocks cannot see the defect (established obstruction).** For the Leavitt
  cover, every sofic approximation preserves the expander blocks of `N`
  (`kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient`). Inside a
  single block, `N`, the compressors and the relative centralizing elements
  all act freely, with `N` ergodic. A proof has to see
  `[g z g^-1, gamma] not in M` from inside one block. Partition, orbit and
  fixed-algebra data carry nothing.
- **Split `sigma(z)` as `sigma(M)` times an exact centralizer (refuted).**
  `relative-defect-via-normalizer-split` would prove this claim, but its
  premise `relative-element-splits-into-m-times-centralizer` is false
  (`outer-automorphism-mod-kernel-refutes-centralizer-splitting`). A splitting
  makes `z` act on `Gamma` as an inner automorphism by `M`. Transpose-inverse on
  `SL_3(Z)`, which is trivial modulo `M = SL_3(Z)`, is not inner. Any repair has
  to tolerate outer automorphisms that are trivial modulo `M`.
- **Exact von Neumann form.** For `d in H`, `d in M` if and only if
  `sigma(d) in W*(sigma(M))`, because `E_(L(M))(u_d) = 0` off `M`. So for the
  defect elements it is enough to show `||E_(W*(sigma(M))) sigma(d)||_2 > 0`.
  Analytic lower bounds therefore suffice, and no exact group identity is
  needed.
- **Canonical trace sees nothing of `H/M`.** At canonical trace the spectral
  measure of `M`'s Laplacian is that of the regular representation. That has
  a gap at `0` and no kernel, so the Kazhdan projection of `M` has trace `0` in
  every trace-preserving model. Hence `H/M` has no representation on a nonzero
  corner of the tracial ultraproduct, and a proof has to work on the diagonal
  (Koopman) side.
