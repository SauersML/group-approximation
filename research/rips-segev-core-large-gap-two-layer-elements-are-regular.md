---
rg: 2
id: rips-segev-core-large-gap-two-layer-elements-are-regular
kind: claim
title: Extreme ports of a zero-divisor walk into signed positive relations, so u + w b with an edge-degree gap beyond the line lengths is regular in the Rips--Segev core group
distinct_from:
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question for all alpha and beta; this settles one explicit class of beta (two b-layers with a large degree gap) against arbitrary alpha.
  rips-segev-witness-supports-carry-no-zero-divisors: that constrains both supports to the witness (A, B); here alpha is arbitrary and only beta is restricted.
  rips-segev-groups-embed-every-torsion-free-group: that proves universality over arbitrary factors and isolates the core group; this is a statement inside the core group, transported to all factors by freeness.
  cyclic-centralizer-groups-have-no-support-three-zero-divisors: that is the support-three case for a broad host class; the class here has arbitrary support but a degree condition, and uses the Rips--Segev graph.
  rips-segev-port-data-cannot-exclude-balanced-divisors: that proves the port method below cannot reach the balanced case; this is the part the port method does reach.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-core-large-gap-two-layer-elements-are-regular-proof`.

**Setting.**  Steenbock, arXiv:1307.0981.
- `Gamma` is a finite generalized Rips--Segev graph whose labelling satisfies `Gr'_*(1/8)`.  Example: Steenbock's
  table `(10^{5i-4}, ..., 10^{5i})` with underlying graph of girth at least 41.
- `K = K_Gamma = (<a> * <b>) / <<R>>` is the core group.  By Step 0 of
  `rips-segev-groups-embed-every-torsion-free-group-proof`, `Gr'_*(1/8)` holds over `F_2 = <a> * <b>`.
- On a-line `i`, `S_i` is the set of source positions of b-edges and `T_i` the set of target positions.
- The **line-difference set** is `Delta(Gamma) = {0} ∪ { q - p : i a line, p in T_i, q in S_i }`.  Write
  `Delta_+ = max Delta` and `Delta_- = min Delta`.
  - Always `|Delta_±| <= N := max_i C_i`.
  - For Steenbock's explicit graphs, `S_i = {0, O_i1, O_i2, C_i}` and `T_i = {0, I_i1, I_i2, C_i}`, so
    `Delta_± = ±N`.
- For a nonzero Laurent polynomial `f in k[<a>]`, `f_+` and `f_-` are its top and bottom exponents.

**Theorem.**  Let `k` be any field and let `u, w in k[<a>]` be nonzero.  Put `beta = u + w b` and
`delta_+ = w_+ - u_+`, `delta_- = w_- - u_-`.

If `delta_+` or `delta_-` lies outside `[Delta_-, Delta_+]`, then `beta` is a non-zero-divisor in `k[K]`: both
`alpha beta = 0` and `beta alpha = 0` force `alpha = 0`.  For Steenbock's graphs the condition reads
`max(|delta_+|, |delta_-|) > N`.

The same holds in `k[G(Gamma)]` for every generalized Rips--Segev group `G(Gamma) = G_1 *_{<a>} K *_{<b>} G_2` over
torsion-free factors, because `k[G]` is a free left and right `k[K]`-module.

**The three steps.**
1. **Port lemma.**  A nonzero `alpha` with `alpha beta = 0` gives, on each left `<a>`-coset `h` meeting
   `supp alpha`, two port sets: `Out_h = supp(alpha_h w)` and `In_h = supp(alpha_h u)`.
   - They satisfy `Out b = In`.
   - On every coset, the top out-port lies `delta_+` above the top in-port, and the bottom out-port lies `delta_-`
     above the bottom in-port.
   - The case `beta alpha = 0` reduces to the same port structure for `w* + b u*`, with `delta_±` swapped.
2. **Walk lemma.**  Any such port configuration forces four positive relations `b a^{n_1} ... b a^{n_L} = 1`,
   with `L >= 1`:
   - one with all `n_k >= delta_+` (following top out-ports forward);
   - one with all `n_k <= delta_+` (top in-ports backward);
   - one with all `n_k <= delta_-` (bottom out-ports forward);
   - one with all `n_k >= delta_-` (bottom in-ports backward).
3. **Positive relation lemma.**  Every positive relation of `K` has some `n_k in Delta(Gamma)`.  The proof is a
   van Kampen case analysis with the graphical small cancellation lemma.

**Calibration.**
- For `Gamma` with no cycles (`K = F_2`) there are no positive relations, so the walk lemma reproduces the fact
  that all these `beta` are regular in `k[F_2]`.
- In `Z × Z/2 = <a> × <b | b^2>`, the element `1 + b` is a zero divisor with `delta_± = 0`.  The walk lemma
  produces `b a^0 b a^0 = 1`, consistent with that.

**Limits.**
- The walk lemma does not use malnormality of `<a>` or the extremal-coset lemma.
- The balanced range `delta_± in [Delta_-, Delta_+]` stays open.  Examples are `1 + a + (1 + lambda a) b` and
  `1 + a + b`.
- `rips-segev-port-data-cannot-exclude-balanced-divisors` shows that no argument using only port data
  can close `delta_+ = delta_- = 0`: the graph `Gamma` itself realizes such a configuration in the Cayley graph.
