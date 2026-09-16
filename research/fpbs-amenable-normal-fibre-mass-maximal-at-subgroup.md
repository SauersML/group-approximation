---
rg: 2
id: fpbs-amenable-normal-fibre-mass-maximal-at-subgroup
kind: claim
title: An amenable normal subgroup carries the largest expected cluster mass among its cosets
distinct_from:
  fpbs-fibre-summed-connectivity-operator: that equates the l2 norm of the connectivity operator with the norm of convolution by the fibre-mass function; this bounds every value of that function by its value at the identity, a pointwise statement valid at every p that needs no operator bound.
  fpbs-tree-projected-branch-share-last-crossing-bound: that bounds fibre masses over a free quotient by products of branching factors that grow with word length; this bounds every fibre mass by the relative susceptibility, uniformly over the quotient, for any amenable normal subgroup and any generating set.
  fpbs-relative-susceptibility-tube-excursion-bound: that bounds the relative susceptibility from above by tube quantities; this bounds the other fibre masses from above by the relative susceptibility.
artifacts:
  - research/artifacts/fpbs-amenable-normal-fibre-mass-bound-2026-09-16.md
---

**ESTABLISHED.**

**Setting.** Let `G = Cay(Gamma,S)` be a Cayley graph of a finitely generated
group, `o` the identity, and `phi_p(g) = P_p(o <-> g)` for Bernoulli(`p`) bond
percolation. For `A ⊆ Gamma` write `chi^A_p = E_p|K_o ∩ A|`.

**Statement.** For every amenable subgroup `H <= Gamma`, every `g in Gamma` and
every `p in [0,1]`,

```text
E_p|K_g ∩ H| = chi^(Hg)_p <= ( chi^H_p · chi^(g^(-1) H g)_p )^(1/2).
```

**The normal case.** If `H` is amenable and normal with quotient `Q = Gamma/H`,
the fibre masses `sigma_p(q) = E_p|K_o ∩ Gamma_q|` satisfy

```text
sigma_p(q) = sigma_p(q^(-1)) <= sigma_p(1) = chi^H_p      for every q in Q.
```

If moreover `chi^H_p < infinity`, then `sigma_p` is a positive definite function
on `Q`.

**Consequences.**
* **Commensurable subgroups.** If `L <= H` has finite index and normal core
  `L_0` in `H`, then `chi^L_p <= chi^H_p <= [H:L_0] chi^(L_0)_p`. So finiteness
  of relative susceptibility depends only on the commensurability class of an
  amenable subgroup.
* **Sphere bubbles.** For normal `H`, the sphere bubbles over `Q` satisfy
  `b_R(p) <= chi^H_p E_p|K_o ∩ pi^(-1) S_Q(R)| <= |S_Q(R)| (chi^H_p)^2`.

**Claims this repairs.** The pointwise bound had been asserted without proof in
Section 4.4 of `research/artifacts/fpbs/docs/relative-susceptibility-reduction.md`.
It is the bound withdrawn on 2026-09-12 from Step 3 of Theorem 4.3 in
`research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md`.

**What it does not give.** It does not make `{p : chi^H_p < infinity}` open
above `p_c`. The sprinkling expansion of the relative susceptibility needs the
fibre bubble `sum_q sigma_p(q)^2` and the fibre operator norm. These entrywise
bounds control neither, since `chi_p = infinity` for `p >= p_c`.

Proof: `fpbs-amenable-normal-fibre-mass-maximal-at-subgroup-proof`.
