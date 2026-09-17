---
rg: 2
id: fpbs-lattice-amenable-subgroup-critical-finiteness-no-gap
kind: claim
title: On high-dimensional lattices the two-point function is summable along a low-rank sublattice at p_c, the fibre profile is square summable, and no p above p_c keeps it summable
distinct_from:
  fpbs-relative-susceptibility-divergence-crux-fails: that exhibits critical relative finiteness without a gap on trees, along nonamenable normal subgroups with a random-walk formula; this does it along an amenable (normal) subgroup, in the mean-field regime, with a square-summable critical fibre profile, so the amenable-subgroup and mean-field hypotheses of the wq-normal lane are both present and still give nothing.
  fpbs-amenable-wq-normal-relative-subcriticality: that is the open gap statement for nonamenable ambient groups; this is a calibration world outside its class (the ambient group is amenable), recording which inputs cannot by themselves force the openness step.
artifacts:
  - research/artifacts/fpbs-lattice-critical-relative-finiteness-2026-09-17.md
---

**ESTABLISHED.** Let `G` be the nearest-neighbour Cayley graph of `Z^d` with
`d >= 11`. Let `H = Z^k x {0}` with `k >= 1` and put `m = d - k`, so
`Q = Z^d/H = Z^m`. Write `tau_p(x,y) = P_p(x <-> y)`, and write the fibre mass as

```text
sigma_p(q) = sum_{h in Z^k} tau_p(0, (h,q)),     q in Z^m,
chi^H_p    = sigma_p(0) = E_p|K_0 ∩ H|.
```

1. **Critical relative finiteness.** If `m >= 3` there is `C < infinity` with
   `sigma_(p_c)(q) <= C (1+|q|)^(-(m-2))` for all `q`. In particular
   `chi^H_(p_c) < infinity`.
2. **Square-summable critical profile.** If `m >= 3`, then `sigma_(p_c)` lies in
   `l^r(Z^m)` for every `r > m/(m-2)`. For `m >= 5` this includes `r = 2`.
3. **No gap.** For every `p > p_c(G)`, `chi^H_p = infinity`.

So `{p : chi^H_p < infinity} = [0, p_c]` is closed and not open, even though the
mean-field prediction of Section 4.2 of
`research/artifacts/fpbs/docs/relative-susceptibility-reduction.md` is true
here, and every rearrangement-invariant `l^r` norm (`r > m/(m-2)`) of the
critical fibre profile is finite.

**Calibration.** The mean-field prediction `chi^H_(p_c) < infinity` needs only
polynomial decay `|x|^(-(d-2))` and codimension `m >= 3`. It does not need
`rho(Q) < 1`. So a verified or assumed critical finiteness, a bubble-type
square-summable fibre profile, or mean-field two-point exponents cannot by
themselves yield the openness step of the target
`fpbs-amenable-wq-normal-relative-subcriticality`. Any such argument must use
nonamenability of `Q = Gamma/H` in the step that turns critical data into
data at some `p > p_c`. The gate that distinguishes this world is the operator
norm of convolution by `sigma_(p_c)` on `l^2(Q)`. For nonnegative kernels on
amenable `Q` that norm equals `||sigma_(p_c)||_1 = chi_(p_c)`, which is infinite
(standard, and not used above).
