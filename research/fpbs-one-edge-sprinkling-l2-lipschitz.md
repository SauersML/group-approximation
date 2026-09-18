---
rg: 2
id: fpbs-one-edge-sprinkling-l2-lipschitz
kind: claim
title: The inverse critical two-point l2 norm is Lipschitz in the edge-weight field, with a fresh-generator constant p
distinct_from:
  fpbs-nonamenability-bounds-critical-connectivity-operator: that conjectures a critical l2 bound on every nonamenable transitive graph; this proves only a perturbation inequality across weight fields on any locally finite graph, needs no transitivity, and moves weights between generator classes, including from weight zero.
  fpbs-gap-survives-product-generator-moves: that compares thresholds under combinatorial generator moves through the spectral margin m(S); this compares two-point operators of one ambient Cayley graph at two weight fields and never uses the margin or the power map.
  fpbs-l2-gap-class-closed-under-local-limits: that passes a uniform norm bound along a sequence of graphs converging locally; this moves along the weight field of one graph and gives openness with an explicit radius, without any uniform bound on the limit side.
  fpbs-critical-sphere-fibre-operator-below-one: that seeks critical l2 on one Cayley graph from a sphere-fibre operator norm; this compares two-point operators of one graph at two weight fields and uses no quotient.
---

**OPEN.** Let `G` be a locally finite graph and let `p <= p'` be two
edge-weight fields in `[0,1)`. Write `tau_p(u,v) = P_p(u <-> v)` for
independent bond percolation with edge probabilities `p_e`, `T_p` for the
kernel `tau_p` on `l2(V)`, and `phi(p) = 1/||T_p||_{2->2}` (with `1/infinity = 0`).
Put `r_e = (p'_e - p_e)/(1 - p_e)`, and let `R` be the symmetric edge-weighted
adjacency with weights `r_e`.

1. **Sprinkling inequality.** Entrywise,

   ```text
   T_{p'}  <=  T_p  +  T_{p'} R T_p .
   ```

2. **Lipschitz bound.** `phi(p') >= phi(p) - ||R||_{2->2}`. Equivalently, if
   `||R|| ||T_p|| < 1` then `||T_{p'}|| <= ||T_p|| / (1 - ||R|| ||T_p||)`.
   Combined with monotonicity in `p`, `phi` is Lipschitz on `[0,1-eps]^E` in the
   sup-norm with constant `deg_max/eps`.
3. **Fresh generators.** On `Cay(Gamma,S)` with `S = S' ⊔ S''` symmetric, let the
   anchor field be `p` on `S'`-edges and `0` on `S''`-edges, so the anchor graph
   is the disjoint union of `<S'>`-coset copies of `Cay(<S'>,S')`. Then `r = p` on
   `S''`-edges exactly, and

   ```text
   p ||A_{S''}||  <  1/||T_p(Cay(<S'>,S'))||   implies   p < p_{2->2}(Cay(Gamma,S)).
   ```

   `S' = empty` is walk counting, `p ||A_S|| < 1`.
4. **Continuity reduction on a critical surface.** Fix a finite symmetric `U`
   and a continuous path `gamma : [0,1] -> [0,1-eps]^U` of per-generator weights.
   The good set `{t : ||T_{gamma(t)}|| < infinity}` is relatively open, and
   `1/||T||` is continuous along `gamma`. It is all of `[0,1]` iff `gamma(0)` is
   good and `inf_t phi(gamma(t)) > 0`.

Proof: `fpbs-one-edge-sprinkling-l2-lipschitz-proof`.

## Attempts

1. **2026-09-17, referee pass on a proof attempt (refuted as a batch).** The
   proof in `fpbs-one-edge-sprinkling-l2-lipschitz-proof` was landed together
   with `fpbs-weighted-surface-continuity-reduces-to-uniform-floor`, and all
   three referees voted refuted on the batch. All three checked this lemma and
   found it correct: the coupling `omega' = omega OR xi`, the split at the last
   omega-closed edge, BK on a finite product space, exhaustion, the Lipschitz
   constant `deg_max/eps`, and the fresh-generator identity. Only one gap was
   named: item 3 says strict `p < p_{2->2}` follows "by definition", but it
   actually needs the openness from item 2. The claim returns to OPEN until a
   separate referee pass confirms it
   (`fpbs-sprinkling-lemma-referee-confirmation`).
