---
rg: 2
id: fpbs-one-edge-sprinkling-l2-lipschitz-proof
kind: route
title: Split at the last sprinkled edge, apply BK in finite volume, and exhaust
target: fpbs-one-edge-sprinkling-l2-lipschitz
requires:
  - fpbs-sprinkling-lemma-referee-confirmation
---

*Demoted 2026-09-17 (referee pass): three referees voted refuted on this
landing, which paired this lemma with
`fpbs-weighted-surface-continuity-reduces-to-uniform-floor`. All three checked
this lemma and found it correct, and only item 3's "by definition" strictness
step was flagged. The route now requires the OPEN gap claim
`fpbs-sprinkling-lemma-referee-confirmation`, so its target derives OPEN. The
text below is kept as an attempt.*

1. **Two-layer coupling.** Give every edge two independent bits: `omega_e` with
   probability `p_e`, and `xi_e` with probability `r_e`. Then `omega` has law
   `P_p`, and `omega' = omega ∨ xi` has law `P_{p'}`, since
   `p_e + (1-p_e) r_e = p'_e`. Both connection events are increasing in
   `(omega, xi)`.
2. **Last sprinkled edge.** Fix a finite edge set `F` and use connections inside
   `F`. Suppose `u <-> v` in `omega'` but not in `omega`.
   * Take a simple `omega'`-open path `gamma` from `u` to `v`.
   * Some edge of `gamma` is `omega`-closed. Let `e = (x,y)` be the last such
     edge, oriented along `gamma`.
   * Then `xi_e = 1`, `gamma[u,x]` is `omega'`-open, and `gamma[y,v]` is
     `omega`-open.
   * These witnesses use disjoint coordinates: the edges of the two segments are
     distinct, and `e` lies on neither.
   So the event lies in the union over oriented `e` of
   `{u <-> x in omega'} □ {xi_e = 1} □ {y <-> v in omega}`.
3. **BK.** All three events are increasing on the finite product space
   `{0,1}^(2|F|)`, and the disjoint occurrence of two increasing events is again
   increasing. Iterating the van den Berg–Kesten inequality gives

   ```text
   tau^F_{p'}(u,v) - tau^F_p(u,v)  <=  sum_{(x,y)} tau^F_{p'}(u,x) r_{xy} tau^F_p(y,v).
   ```

4. **Norms in finite volume.** For nonnegative kernels, `0 <= X <= Y` entrywise
   implies `||X|| <= ||Y||`. Put `M = ||T_p||`. Since `T^F_p <= T_p` and
   `R_F <= R`,

   ```text
   ||T^F_{p'}|| <= M + ||T^F_{p'}|| ||R|| M.
   ```

   The left side is finite because `F` is finite. If `||R|| M < 1`, then
   `||T^F_{p'}|| <= M/(1-||R||M)`.
5. **Exhaustion.** As `F` increases to `E`, `tau^F_{p'}` increases to `tau_{p'}`,
   because an open path is finite. For a nonnegative kernel the norm is a
   supremum of `<X f, g>` over finitely supported nonnegative `f` and `g`, so
   monotone convergence gives the same bound for `||T_{p'}||`. Rearranging gives
   the Lipschitz form, and the case `||R||M >= 1` is trivial.
6. **Fresh generators.** With `p_e = 0` on `S''`-edges we get `r_e = p` there and
   `r_e = 0` on `S'`-edges, so `R = p A_{S''}`. The anchor field closes every
   `S''`-edge, so `T_p(anchor)` is block diagonal over `<S'>`-cosets, each block a
   copy of `T_p(Cay(<S'>,S'))`. Item 2 bounds `||T_p(Cay(Gamma,S))||`, and
   `p < p_{2->2}` follows by definition.
7. **Continuity.** For general fields `q` and `q'`, compare both with `q ∨ q'` using
   monotonicity: `phi(q') >= phi(q ∨ q') >= phi(q) - ||R_{q ∨ q' - q}||`. The
   weights of `R` are at most `|q-q'|_inf/eps`, so `||R|| <= deg_max |q-q'|_inf/eps`.
   By symmetry, `phi` is Lipschitz. Along `gamma`, `phi o gamma` is then
   continuous. If `inf phi > 0` every point is good. Conversely, a positive
   continuous function on `[0,1]` has a positive minimum.
