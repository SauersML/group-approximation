---
rg: 2
id: fpbs-normal-fibre-second-moment-maximal
kind: claim
title: For every normal subgroup the cluster's second fibre moment is largest on the subgroup itself
distinct_from:
  fpbs-amenable-normal-fibre-mass-maximal-at-subgroup: that bounds the first fibre moment on cosets of an amenable normal subgroup; this bounds the second moment on every coset of an arbitrary normal subgroup, amenable or not, by a mass-transport and Cauchy--Schwarz bootstrap.
  fpbs-hp-relative-sharpness: that gives exponential tails of |K_o ∩ H| below the relative threshold; this transfers any such moment bound from the subgroup to all of its cosets uniformly.
---

**ESTABLISHED.** Let `G = Cay(Gamma,S)` for a finitely generated group
`Gamma`, let `N` be a normal subgroup of `Gamma`, and let `0 < p <= 1`. Write
`K_o` for the cluster of the identity under Bernoulli(`p`) bond percolation,
and for `q in Gamma` put

```text
X = |K_o ∩ N|,   Y_q = |K_o ∩ qN|.
```

Then for every `q in Gamma`,

```text
E_p[Y_q^2] <= E_p[X^2].
```

**Corollary.** Suppose `p < p_c(N;G)`. By Hutchcroft--Pan relative sharpness
(`fpbs-hp-relative-sharpness`), `E_p[X^2] < infinity`, and so

```text
sup_{q in Gamma} E_p|K_o ∩ qN| <= (E_p[X^2])^(1/2) < infinity.
```

So below the relative threshold of any normal subgroup, the expected mass of
the cluster on one fibre is uniformly bounded over fibres. In a gap window
`p_c(G) < p < p_c(N;G)`, the divergent susceptibility
`chi_p = sum_{qN in Gamma/N} E_p|K_o ∩ qN|` must therefore spread over
infinitely many fibres, and no single coset can concentrate it.

The inequality itself uses no amenability of `N` or `Gamma/N` and no
sharpness input. Only the corollary imports relative sharpness.

DERIVATION
fpbs-normal-fibre-second-moment-maximal-proof
