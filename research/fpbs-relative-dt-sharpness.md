---
rg: 2
id: fpbs-relative-dt-sharpness
kind: claim
title: Relative Duminil-Copin--Tassion sharpness, the Green threshold of the pushed DT boundary measure equals the relative threshold of every infinite normal subgroup
distinct_from:
  fpbs-relative-dt-green-threshold-splits-identity-e: that proves p^G <= p_c(N;G) and that E is (E-a) and (E-b) together; this is the open equality (E-a) alone.
  fpbs-transitive-sharpness-linear-lower-bound: that is DT's sharpness on the whole graph (imported through the route fpbs-duminil-copin-tassion-sharpness-input), whose proof is the case N = Gamma (Q trivial), where the Green certificate is DT's phi_p(S) < 1 and the equality is their theorem; this asks for it along every infinite normal N, where the certificate is a return rate of a non-symmetric chain on Q.
  fpbs-relative-threshold-is-quotient-l2-threshold: that is Claim E, p_c(N;G) = p^Q; this is strictly weaker (it drops the l2 half) and holds on the nonunimodular horocycle calibration where the analogue of E fails.
  fpbs-hp-relative-sharpness: that is Hutchcroft--Pan's relative sharpness (exponential tail of |K_o ∩ H| below p_c(H;G), by OSSS), an infinite-volume statement; this asks for a finite-volume certificate, one finite S whose pushed DT measure has a summable Green function on Q, at every p < p_c(N;G).
---

**OPEN.**

**Statement (E-a).** Let `G = Cay(Gamma, D)` be a Cayley graph of a
finitely generated group, `N` an infinite normal subgroup, `Q = Gamma/N`.
With `mu_{S,p}`, `a_S`, `D_p(S)` and `p^G(N;G)` as in
`fpbs-relative-dt-green-threshold-splits-identity-e`,

```text
p^G(N;G) = p_c(N;G),
```

that is, for every `p < p_c(N;G)` some finite `S` containing `o` has
`D_p(S) = sum_k (mu_{S,p}^{*k} * a_S)(e_Q) < infinity`. By item 2 of that
node it is equivalent to: for every `p < p_c(N;G)` some finite `S` has
return rate `r_p(S) < 1`.

**Why it matters.** Item 5 of the split node: under (E-a), a Kesten gap
`p_c < p_c(N;G)` is equivalent to one finite `S` with `r_{p_c}(S) < 1`, a
finite-volume certificate at `p_c` that is not an l2 condition. So (E-a)
turns the Kesten premise into a finite-volume statement at criticality, and
by item 4 it leaves only (E-b) between the board and Claim E.

**Known cases.**

- `Q` trivial: DT's `p~_c = p_c` (item 4 of the split node).
- `Q` amenable: all four thresholds equal `p_c` (item 4 of the split node,
  via `fpbs-amenable-quotient-normal-relative-threshold-is-pc`).
- Every class where Claim E is ESTABLISHED, since E implies (E-a) by item 4:
  tree Cayley graphs (`fpbs-tree-cayley-graphs-satisfy-identity-e`),
  free products along commuting quotients
  (`fpbs-free-product-commuting-quotients-satisfy-identity-e`), complete-block
  free products (`fpbs-complete-block-free-products-satisfy-identity-e`).
- The transitive nonunimodular analogue on `T_k` horocycles:
  `p^G(L) = p_c(L;T_k) = 1/sqrt(k-1)` (item 8 of the split node).

## Attempts

**Where it can fail (invariant).** At `(G,N,p)` with `p < p_c(N;G)`, so
`chi^N_p < infinity`, while `inf_S r_p(S) >= 1`. The invariant is the
return rate `inf_S r_p(S)` of the pushed chain.

- DT's proof for `Q` trivial runs a differential inequality in `p` whose
  coefficient is `inf_S phi_p(S)`, a total mass. For nontrivial `Q`, the
  return rate is not a mass: `mu_{S,p}` can have mass above one and return
  rate below one (item 8 of the split node, on `T_k` horocycles, is exactly
  this). A relative DT inequality must replace `phi_p(S)` by a quantity
  controlled by the return rate, and the one-step inequality of DT does
  not see where on `Q` the boundary mass sits.
- Why HP's relative sharpness does not give it. `fpbs-hp-relative-sharpness`
  gives `chi^N_p < infinity`, and even exponential tails of `|K_o ∩ N|`, at
  every `p < p_c(N;G)`. Going from there to a finite `S` needs the reverse of
  item 1 of the split node (a lower bound on `chi^N` by the Green function of
  a finite-volume chain). For `Q` trivial that reverse bound is DT's
  mean-field lower bound, `theta(p') > 0` for every `p' > p~_c`. A relative version is
  not on the board.
- Heuristic only (2026-09-20, swarm-0917-w23-w23-bs-follow; not attempted
  as a proof). A Russo formula for `chi^N` with pivotal boundary edges pushed
  to `Q` produces one-step quantities of the form
  `sum_q mu(q) sigma^N(q)`. The Green function sums over all chains, so the
  expected missing ingredient is a renewal at the DT boundary that keeps
  track of the landing coset. This was not checked beyond this sketch.
