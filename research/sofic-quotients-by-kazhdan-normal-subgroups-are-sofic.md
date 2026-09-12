---
rg: 2
id: sofic-quotients-by-kazhdan-normal-subgroups-are-sofic
kind: claim
title: The quotient of a sofic group by a normal Kazhdan subgroup is sofic
distinct_from:
  flexible-p-stability-passes-to-fg-normal-quotients: that passes flexible permutation stability down to quotients by finitely generated kernels; this asks whether soficity itself passes to quotients by Kazhdan kernels.
  sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels: that asks only that such quotients satisfy the rigid-defect criterion; this asks that they be sofic, which implies it.
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

**OPEN.** If `H` is a countable sofic group and `M` is a normal subgroup of `H`
with property (T), then `H/M` is sofic.

It implies `sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels`, and
through it a nonsofic hyperbolic group. If every hyperbolic group is sofic,
the Leavitt cover `hyperbolic-kazhdan-cover-of-leavitt-unit-group` refutes
it.

## Attempts

- **The kernel hypothesis cannot be dropped.** A free group maps onto the
  nonsofic `R^x`, with a free kernel that is not Kazhdan. So property (T) of
  `M` has to be used.
- **Finite models separate nothing.** In the Leavitt cover, every finite image
  of `G` is already the image of `N`
  (`hyperbolic-kazhdan-cover-of-leavitt-unit-group`). Even if `G` is
  residually finite, its finite quotient actions give `R^x` only the trivial
  action on `N`-orbits. Residual finiteness of `H` gives no model of `H/M`
  here. Dead for this host.
- **Canonical trace.** The Kazhdan projection of `M` has trace `0` in every
  trace-preserving model of `H`, so `H/M` acts on no nonzero corner of the
  tracial ultraproduct (see the claim above). A proof would have to discretize
  the `M`-invariant diagonal factor instead. Where the discretization dies:
  `H/M` acts on that factor without any freeness.
- **Block-level reformulation.** By
  `kazhdan-quotient-sofic-iff-injective-block-representation` (established),
  `H/M` is sofic iff some sofic approximation of `H` moves the `M`-expander
  blocks by an injective representation of `H/M`. Consequences:
  - this claim is equivalent to producing such an approximation from soficity
    of `H` alone;
  - one approximation can give the trivial block representation even when
    `H/M` is sofic, so a proof has to construct new approximations of `H`;
  - the one known construction, a product with an approximation of `H/M`, is
    circular.
  No non-circular construction is known.
- **Residually finite hosts with a closed kernel.** If `H` is residually
  finite and `M` is closed in the profinite topology, then `H/M` is residually
  finite, hence sofic, so the claim holds in that case. Coset models give an
  injective block representation exactly when the finite quotients
  `H/MK` separate `H/M`. The Leavitt cover is the opposite extreme: `N` maps
  onto every finite quotient.
- **Flexible permutation stability adds nothing beyond that case.**
  - If `H` is flexibly P-stable, its approximations correct to genuine finite
    actions (`flexible-p-stability-passes-to-fg-normal-quotients`).
  - Kernel orbits there are expanders for `S`, hence the blocks, and they are
    cosets of `MK` in each transitive piece `H/K`.
  - So the block representations are actions of `H/M` on finite quotients.
  - Stability therefore gives soficity of `H/M` only along separating finite
    quotients, i.e. the residually finite case above.
