---
rg: 2
id: fpbs-harris-chain-majorant-is-superexponential
kind: claim
title: The Harris same-cluster majorant of the fibre-kernel powers has super-exponential growth at every p on every graph, so it can never certify quotient l2 boundedness
distinct_from:
  fpbs-bk-majorant-kesten-gap-is-quotient-critical-l2: that kills Russo-BK integration upward from p_c, with invariant the critical quotient norm; this kills Harris-FKG domination of the multi-chain fibre powers at a single parameter, with invariant the tuple-versus-chain count, and it applies at every p including p < p_c.
  fpbs-soft-collapse-kills-relative-gap-proofs: that kills proofs using only invariance, ergodicity, insertion tolerance and FKG-type soft inputs of the limit family; this is a quantitative failure of one Bernoulli correlation inequality, Harris-FKG, applied to chain products, on Bernoulli percolation itself.
  fpbs-quotient-l2-threshold-sandwich: that supplies the diagonal formula used here; this is an obstruction to one way of bounding the diagonal.
artifacts:
  - experiments/fpbs-fkg-chain-majorant-2026-09-17/tree_cluster_moments.py
  - experiments/fpbs-fkg-chain-majorant-2026-09-17/output.txt
---

**ESTABLISHED.** Proof route:
`fpbs-harris-chain-majorant-is-superexponential-proof`.

**Setting.**
- `G` is an infinite, connected, locally finite, vertex-transitive graph
  (for example a Cayley graph), with root `o`.
- `N` is any set of vertices containing `o`. The main case is an infinite
  normal subgroup `N` of `Gamma`, with `G = Cay(Gamma,S)` and `Q = Gamma/N`.
- `P_p` is Bernoulli bond percolation, `tau_p(x,y) = P_p(x <-> y)`,
  `K_o` is the open cluster of `o`, `chi_p = E_p|K_o|`, and `theta(p) = P_p(|K_o| = infinity)`.

**The chain sum.** For `m >= 1` put

```text
C_m(p) = sum_(x_1,...,x_(m-1) in V, y in N) tau_p(o,x_1) tau_p(x_1,x_2) ... tau_p(x_(m-1),y).
```

For normal `N` this is `sigma_p^(*m)(e)`, the `m`-th convolution power of the
fibre-summed kernel `sigma_p(q) = sum_(x in q) tau_p(o,x)` on `Q`. By the
diagonal formula of `fpbs-quotient-l2-threshold-sandwich`,
`||sigma_p||_(l2(Q)) = limsup_m C_(2m)(p)^(1/(2m))`. Bounding `C_m(p)`
exponentially in `m` is therefore the whole content of type (i) certificates
and of the weak identity `E'` in `fpbs-relative-threshold-is-quotient-l2-threshold`.

**The Harris majorant.** The events `{x_(i-1) <-> x_i}` are increasing, so
Harris--FKG gives `prod_i tau_p(x_(i-1),x_i) <= P_p(o,x_1,...,x_(m-1),y all in one cluster)`. Summing,

```text
C_m(p) <= H_m(p) := E_p[ |K_o|^(m-1) |K_o ∩ N| ].
```

**Theorem.** For every such `G`, `N`, `p in (0,1)` and `m >= 2`:

1. **Above p_c.** If `theta(p) > 0`, then `H_m(p) = infinity`.
2. **Everywhere.** `H_m(p) >= (m p)^(m-1)`, so `H_m(p)^(1/m) -> infinity` as
   `m -> infinity`.
3. **Loss where the target is trivial.** For `p < p_c`,
   `C_m(p) <= chi_p^m`, while `H_m(p)/chi_p^m >= (m p/chi_p)^(m-1)/chi_p`.
   So the majorant loses a super-exponential factor even where the true chain
   sum grows at most exponentially.
4. **Any single-parameter same-cluster count.** Parts 1--3 hold with `p`
   replaced by any `p'` for every majorant of the form
   `C_m(p) <= E_(p')[Phi_m(K_o)]` with
   `Phi_m(K) >= #{(x_1,...,x_(m-1),y) in K^(m-1) x (K ∩ N)}`. That includes
   superposition of the `m` factors into one configuration, where
   `p' = 1-(1-p)^m >= p`.

**What this kills (obstruction).** The class is every proof of type-(i)
certification, of `E'`, or of critical fibre l2
(`||sigma_(p_c)||_(l2(Q)) < infinity`) that bounds the multi-chain powers
`C_m` by counting tuples of points in one percolation cluster at one
parameter. This covers Harris--FKG chain domination, cluster-moment bounds,
and exponential tails of `|K_o|` or of `|K_o ∩ N|` (relative sharpness)
applied to tuple counts.
- **Invariant.** The ratio of ordered tuples in one cluster to chains of
  independent connections, `H_m/C_m >= (m p/chi_p)^(m-1)/chi_p` below `p_c`
  and `+infinity` above it.
- **Step where every member dies.** Passing from
  `C_m(p) <= E_(p')[Phi_m(K_o)]` to a bound `C^m`. It dies at every `p`, on
  every graph and for every `N`, including trees, where `E` is proved.

**What survives.** The other classical correlation inequalities (BK, Reimer)
bound disjoint-witness events from above. So they bound `C_m` from below,
not from above. An upper bound on `C_m` must therefore keep the product
structure of the chain. Two known ways do this:
- a renewal or resolvent identity (free products,
  `fpbs-free-product-commuting-quotients-satisfy-identity-e`);
- a spectral cluster functional such as the Gram bound
  `||sigma_p||_Q <= E_p[|K|^(-1) ||lambda_Q(a_K)||^2]`
  (the swarm-0917 w18 bus lemma `fpbs-normal-fibre-mass-cluster-gram-representation`,
  which is not yet in this tree).

Neither is an event count.

**Numerical calibration.** On `T_3` at `p < 1/2`, exact Galton--Watson
cluster laws give `(E|K|^m)^(1/m)/chi_p` equal to 7.9 at `p = 0.2`, 15.3 at
`p = 0.35` and 37.2 at `p = 0.45`, for `m = 20`. It grows linearly in `m`,
while `C_m^(1/m) <= chi_p`. See the artifacts.
