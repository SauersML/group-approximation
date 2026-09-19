---
rg: 2
id: sign-mark-rate-is-sector-density
kind: claim
title: For a sign mark the amplification rate is exactly the negative sector density
distinct_from:
  corner-renormalization-cost: That claim is the general norm bookkeeping for compression; this one evaluates the effective-rank stopping statistic for a specific shape of mark and reads off which candidate families are rate-blocked.
  mf-trace-gap-defect-ratio-models: That open claim asks for models achieving the profile; this established one computes what the profile says for a central involution, and identifies where it is free and where it provably fails.
artifacts:
  - notes/FALSE_WEAK_MF_EFFECTIVE_RANK_PROFILE.md
  - notes/CENTRAL_RADICAL_SHEAR_GADGET.md
  - notes/NON_MF_TO_HYPERLINEAR_DIFFERENTIAL_AUDIT.md
---

Let `z` be a central involution and `phi_n` operator-norm models with defect
`epsilon_n` in which `phi_n(z)` is (asymptotically) a self-adjoint involution
with negative spectral sector of relative dimension

```text
delta_n = r_n/d_n.
```

Then the effective-rank stopping statistic `(ERP11)` of
`FALSE_WEAK_MF_EFFECTIVE_RANK_PROFILE.md` is

```text
epsilon_n^2 d_n / ||phi_n(z)-1||_F^2 = epsilon_n^2/(4 delta_n),   (SD1)
```

so the whole profile collapses to one number, the sector density, and:

1. if `liminf delta_n > 0` the mark is already Hilbert--Schmidt visible,
   `1-Re tr(phi_n(z)) = 2 delta_n`, and **no amplification is needed at all**;
2. otherwise the profile is exactly `epsilon_n = o(sqrt(delta_n))`, which is
   the corner-renormalization cost `tau(p_n)^(-1/2) = delta_n^(-1/2)` of
   `corner-renormalization-cost` in rate form.

Reading the two candidate families through `(SD1)`:

* **Clifford family.**  The Connes-embeddable Clifford detector sends the mark
  to the scalar `-1`, so `delta_n = 1` and the statistic is `epsilon_n^2/4`.
  The rate is free; that family's difficulty was never the rate.
* **Cyclic-shear family.**  `J(H,x) = (H x <z>) *_A K` amalgamates over the
  finite `A = <x,z> = C_2 x C_2`, and `alpha(x)=xz` makes the compressor swap
  the two characters with `chi(z) = -1`, so those two sectors have equal
  rank.  In any splice matching the vertex models along a multiple of the
  regular representation of `A` --- which is what an amalgam criterion asks
  for --- `delta_n = 1/2` and the statistic is `epsilon_n^2/2`.  The rate is
  free; the blocker is existence of the total-group model, the
  projective-sector splice.
* **Free-lamp family with exact ambient letters.**  Here property `(T)`
  rigidity forces `||phi_n(q)-1||_(2,d_n) <= C epsilon_n`, i.e.
  `delta_n <= C^2 epsilon_n^2/2`, and `(SD1)` is bounded below by `1/(2C^2)`.
  The rate provably fails.

So the rate is not the blocker in either named candidate family; it is the
blocker exactly where property `(T)` squeezes the mark onto a vanishing
sector, and there it fails rather than being unknown.
