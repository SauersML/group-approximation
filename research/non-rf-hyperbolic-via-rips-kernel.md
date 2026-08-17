---
rg: 2
id: non-rf-hyperbolic-via-rips-kernel
kind: route
title: Hide a non-residually-finite quotient behind a finite-quotient-free Rips kernel
target: non-residually-finite-hyperbolic-group
requires:
  - rips-kernel-without-finite-quotients
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

Suppose `1 → N → G → Q → 1` with `G` hyperbolic, `Q` finitely presented and
not residually finite, and `N` with no nontrivial finite quotient.  Then `G`
is not residually finite.

Proof.  Let `φ : G → F` be any homomorphism to a finite group.  Its
restriction to `N` has image a finite quotient of `N`, hence trivial, so `φ`
kills `N` and factors through `Q`.  Choose `1 ≠ q ∈ R_f(Q)` and any `g ∈ G`
with image `q`; then `g ≠ 1`, and every finite quotient of `G` sends `g` to
the image of `q` under a finite quotient of `Q`, which is trivial.  So

```text
1 != g in R_f(G).
```

The argument is two lines and uses nothing about hyperbolicity; all the
weight sits on the input claim `rips-kernel-without-finite-quotients`, which
is where Belegradek--Osin stop.

**The circularity that is not there, and the one that is.**  Reading "`N` is a
quotient of a hyperbolic group with no finite quotients" as circular is a
mistake: quotients of residually finite groups routinely have no finite
quotients.  The real hazard is different and is recorded on the input claim —
the existing construction gives no handle on the finite residual of `N`, and
the one handle its authors describe (start from a hyperbolic group with no
finite quotients) is *equivalent* to the answer.  A proof of the input claim
must therefore force the property from the small-cancellation data itself.
