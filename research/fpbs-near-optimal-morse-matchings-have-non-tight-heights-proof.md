---
rg: 2
id: fpbs-near-optimal-morse-matchings-have-non-tight-heights-proof
kind: route
title: Unfold recovery trees to bound recovery length by (k-1)^height, then charge long routes to high removed edges in the routing tail inequality
target: fpbs-near-optimal-morse-matchings-have-non-tight-heights
requires:
  - fpbs-bernoulli-morse-collapse-criterion
  - fpbs-quantitative-routing-tail-bound
---

Notation is as in the target. "Theorem A" is Theorem A of the artifact of `fpbs-bernoulli-morse-collapse-criterion`.
Its proofs of (a) and (b) use only that the action is essentially free and measure preserving. The Bernoulli
hypothesis is used only in (c), which is not needed here. So for every essentially free p.m.p. action:

- recovery trees are almost surely finite;
- `Phi'` generates the orbit relation;
- `c(Phi') = |S| - mu(M)`.

**Step 1: height to modulus (item 1).** We use induction on `H >= 1`. Let `e` be in `E_M` with `ht(e) <= H`, and let
`c = M^{-1}(e)`.

- By (M1), `e` is traversed once by the boundary path of `c`. That path has length at most `k`.
- So deleting `e` leaves a path `p` from one endpoint of `e` to the other, with at most `k - 1` edges.
- Each edge of `p` is either retained, which is a `Phi'`-path of length `1`, or a child `e'` of `e` with
  `ht(e') <= H - 1`.
- If `H = 1`, there are no children, so `p` is a `Phi'`-path of length at most `k - 1`.
- If `H >= 2`, the induction hypothesis joins the endpoints of each child by a `Phi'`-path of length at most
  `(k-1)^(H-1)`. Since `k >= 2`, that is at least `1`, so it also bounds retained edges.
- Concatenating gives a `Phi'`-path of length at most `(k-1)(k-1)^(H-1) = (k-1)^H`.

Retained edges are joined by paths of length `1 <= (k-1)^H`. Removed edges of height at most `H` are covered by the
induction above. Hence, for every `H >= 0` and every edge of `Phi_S` outside `E_M^{>H}`, the endpoints are at
`Phi'`-distance at most `(k-1)^H`. For `H = 0` this is the statement for retained edges.

**Step 2: the invariant subgraph.**

- Transport `Phi'` to `G` by the orbit map `g -> g^-1 . x`. Freeness makes this a graph isomorphism from `G` onto the
  `S`-Schreier graph of the orbit of `x`, sending `{g, g t}` to `{g^-1 x, t^-1 g^-1 x}`.
- Let `H'_x` be the simple subgraph of `G` whose edges correspond to edges of `Phi'`. Then `x -> H'_x` is a Borel
  equivariant map, so its law is an invariant random subgraph of `G`.
- It is spanning, and it is connected almost surely by Theorem A(a).
- Each simple edge at the root comes from at least one graphing edge at `x` or at a neighbour, so
  `E deg_{H'}(o) <= 2 c(Phi')`. Hence `delta := E deg_{H'}(o)/2 - 1 <= c(Phi') - 1 = |S| - 1 - mu(M)`.

**Step 3: charging the tail.** Put `r = (k-1)^H`. Fix `t` in `S ∪ S^-1`.

- By Step 2, `d_{H'}(o, t)` is the `Phi'`-distance from `x` to `t^-1 x`, the `t`-neighbour of `x` under the
  isomorphism.
- The simple edge `{x, t^-1 x}` is realised in `Phi_S` by the graphing edge `(x, t^-1)` if `t^-1` is in `S`, and by
  `(t^-1 x, t)` if `t` is in `S`.
- By Step 1, if `d_{H'}(o, t) > r`, then one of these realisations lies in `E_M^{>H}`. The Step 1 bound applies to
  every realisation outside `E_M^{>H}`, and each realisation joins the same two points.
- Sum over `t`. The map `t -> t^-1` is a bijection of `S ∪ S^-1`, and measure preservation moves the base point from
  `t^-1 x` to `x`. So every `s` in `S` contributes `nu_s := mu{x : (x, s) in E_M^{>H}}` at most twice:

  ```text
  sum_{t in S ∪ S^-1} P(d_{H'}(o, t) > r) <= 2 sum_{s in S} nu_s = 2 nu(E_M^{>H}).
  ```

**Step 4: apply the routing tail inequality (item 2).**

- `fpbs-quantitative-routing-tail-bound` applies to `H'`, since it is an invariant random connected spanning subgraph
  of the nonamenable `d`-regular Cayley graph `G`.
- It gives `(1/d) sum_t P(d_{H'}(o, t) > r) >= h/d - delta |B_G(o, r)|`.
- Use Step 3 on the left. On the right, use `delta <= |S| - 1 - mu(M)` and `|B_G(o, r)| > 0`.
- Multiplying by `d` gives item 2.
- If `Gamma` is amenable, then `h = 0` and item 2 is trivial, because its left side is nonnegative and its right side
  is at most `0`.

**Step 5: item 3.** If every height is at most `H`, then `E_M^{>H}` is empty and item 2 reads
`0 >= h - d(|S| - 1 - mu(M)) |B_G((k-1)^H)|`. Rearranging gives item 3.

**Step 6: the Reading bullets.**
- *Fixed lists.* Fix `R` and `H`. Then `k` and `|B_G((k-1)^H)|` are fixed, so `eta(M_j) -> 0` makes the subtracted
  term vanish, and item 2 gives `liminf_j nu(E_{M_j}^{>H}) >= h/2`.
- *Depth one.* A depth-one matching over `P_L` has `k <= L` and all heights equal to `1`, so item 3 gives
  `eta(M) >= h / (d |B_G(L-1)|)`. Since `|B_G(L-1)| <= 1 + d + ... + d^(L-1) <= d^L` for `d >= 2`, we get
  `d^L >= h / (d eta(M))`, and taking `log_d` gives the stated bound.
- *Target.* This bullet is item 2 applied to each `M_j`, with `k <= L_j`, so that `(k-1)^H <= (L_j-1)^H`.
- *Deficit.* The identification of `eta(M)` with the Morse deficit when `beta_1^(2) = 0` is the definition
  `m = z(Phi_S) - mu` together with `z(Phi_S) = |S| - 1 - beta_1^(2)`, imported in the collapse-criterion artifact
  as (I).

QED.
