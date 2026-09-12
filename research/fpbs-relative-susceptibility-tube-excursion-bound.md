---
rg: 2
id: fpbs-relative-susceptibility-tube-excursion-bound
kind: claim
title: Relative susceptibility along a cyclic normal subgroup is a tube term plus one fibre-sphere bubble
distinct_from:
  fpbs-bs-iff-finite-relative-susceptibility: that proves threshold separation equals finite relative susceptibility above p_c; this bounds the relative susceptibility at every p by a tube quantity finite for all p<1 plus the excursion bubble over one sphere of the quotient.
  fpbs-amenable-wq-normal-relative-subcriticality: that is the open premise that relative susceptibility is finite just above p_c; this is a proved inequality locating all possible divergence in excursions to far fibres.
artifacts:
  - research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md
---

**ESTABLISHED.** Let `Gamma` be finitely generated with an infinite cyclic
normal subgroup `H = <z>`. Let `Q = Gamma/H`, let `S` be a finite symmetric
generating set, and let `sigma_p(q) = E_p|K_o ∩ q|`. For `r >= 0` let
`T_r = pi^(-1)(B_Q(r))` be the tube, and let `C_r(p)` be the expected number of
points of `H` joined to `o` inside `T_r`. Then for every `p < 1` and `r >= 0`,

```text
E_p|K_o ∩ H|  <=  C_r(p)  +  sum_{q in S_Q(r+1)} sigma_p(q)^2,
```

where `C_r(p) < infinity` is nondecreasing in `p`.

The tube is quasi-one-dimensional: `H` acts on it cocompactly, and bounded
level cuts close with probability at least `(1-p)^(M_r)`. An open path that
leaves `T_r` first exits through a fibre over `S_Q(r+1)`. BK at that vertex,
summed along the fibre, gives the sphere bubble. Proof: artifact Lemma 4.1.
