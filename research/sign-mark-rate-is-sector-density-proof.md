---
rg: 2
id: sign-mark-rate-is-sector-density-proof
kind: route
title: Evaluate the stopping statistic on an involution and read the three families
target: sign-mark-rate-is-sector-density
requires: []
artifacts:
  - notes/FALSE_WEAK_MF_EFFECTIVE_RANK_PROFILE.md
  - notes/CENTRAL_RADICAL_SHEAR_GADGET.md
---

## Direct proof

**The identity `(SD1)`.**  If `u` is a self-adjoint unitary on `C^d` whose
`-1`-eigenspace has dimension `r`, then `u-1` has eigenvalue `-2` with
multiplicity `r` and `0` otherwise, so

```text
||u-1||_F^2 = 4r,   ||u-1||_op = 2,   r_eff(u-1) = 4r/4 = r,
1-Re tr_d(u) = 2r/d.
```

Substituting into `(ERP1)`--`(ERP2)` gives
`epsilon^2 d/||u-1||_F^2 = epsilon^2 d/(4r) = epsilon^2/(4 delta)`, which is
`(SD1)`; if `phi_n(z)` is only asymptotically an involution, round it by
continuous functional calculus first, which perturbs each displayed quantity
by `o(1)`.  Item 1 is `1-Re tr = 2 delta` bounded below, item 2 is `(SD1)`
tending to `0` iff `epsilon_n^2/delta_n -> 0`.

**Clifford family.**  `notes/NON_MF_TO_HYPERLINEAR_DIFFERENTIAL_AUDIT.md`
records that the Clifford tower detector sends the mark to `-1`; a scalar
`-1` on `C^d` has `r = d`, so `delta = 1`.

**Cyclic-shear family.**  In `notes/CENTRAL_RADICAL_SHEAR_GADGET.md` the mark
is the central involution `z = [s,x]` of `J(H,x) = B *_A K` with
`B = H x <z>`, `A = <x,z> = C_2 x C_2`, `K = A semidirect <s>`, and
`alpha(x) = xz`, `alpha(z) = z`.  Characters of `A` are pairs
`(chi(x),chi(z))`; composing with `alpha` fixes both characters with
`chi(z)=+1` and interchanges the two with `chi(z)=-1`.  Conjugation by
`phi_n(s)` implements `alpha` up to `epsilon_n` and preserves rank, so the
two `chi(z)=-1` isotypic sectors have equal rank up to `o(d_n)`.  If the
restriction of the model to `A` is a multiple of the regular representation
of `A`, all four characters have density `1/4` and `delta_n = 1/2`.

**Free-lamp family with exact ambient letters.**  This is `(ERP9)`--`(ERP10)`
of `FALSE_WEAK_MF_EFFECTIVE_RANK_PROFILE.md`: with exact finite-dimensional
ambient letters and an almost-central lamp, property `(T)` gives
`||phi_n(q)-1||_(2,d_n) <= C epsilon_n`, i.e.
`||phi_n(q)-1||_F^2 <= C^2 epsilon_n^2 d_n`, so the statistic is at least
`1/C^2`.  In sector form, `1-Re tr = 2 delta_n <= C^2 epsilon_n^2`.  End
proof.

## What this reallocates

Effort spent extracting a rate from the shear or Clifford families is
misallocated: `(SD1)` is `o(1)` there for free.  The live question in the
shear family is the projective-sector splice that would produce a
total-group model at all, and in the free-lamp family it is whether the
ambient letters can be made genuinely approximate --- since with exact
ambient letters the rate is refuted, not open.
