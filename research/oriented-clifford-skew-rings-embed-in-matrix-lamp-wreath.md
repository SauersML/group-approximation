---
rg: 2
id: oriented-clifford-skew-rings-embed-in-matrix-lamp-wreath
kind: claim
title: Clifford skew rings of orientable invariant graphs embed in the matrix-lamp wreath, which embeds in the complete-graph skew ring
distinct_from:
  clifford-cover-group-algebra-splits-into-wreath-and-skew-ring: that identifies the anti-central factor A_S of one Clifford cover; this embeds A_S for every orientable graph into one matrix-lamp crossed product and that into the complete-graph factor over three copies of the sites.
  residual-lamp-quotients-handle-monomial-actions: that proves stable finiteness for lamp values twisted by group automorphisms; the target algebra here is a crossed product twisted by characters (coordinate flips), which that theorem does not cover.
artifacts:
  - research/artifacts/clifford-skew-ring-matrix-lamp-wreath-2026-09-12.md
---

Let `k` be a field with `char k != 2`, `G` a group, `X` a `G`-set, `S` a `G`-invariant loopless graph on `X`,
and `q : X -> F_2` invariant. `A_S = C_S semidirect G` is the Clifford skew group ring of
`clifford-cover-group-algebra-splits-into-wreath-and-skew-ring`.
`B_X = (tensor_X M_2(k)) semidirect G` is the matrix-lamp wreath, with `G` permuting tensor factors.

1. **Spin embedding.** Suppose `S` has a `G`-invariant orientation with finite out-degree. Then
   `c_x -> p_x s_x^q(x) prod_(y in N+(x)) s_y` extends to an injective unital map `A_S -> B_X`.
   - This covers the compressor graph `S_psi`, where `psi(g Gamma) = g u^-1 Gamma` and
     `u Gamma u^-1 < Gamma`.
   - Its form `b_(S_psi)` is nondegenerate.
2. **Matching and complete graphs.** `B_X` is the Clifford skew ring of the perfect matching on
   `X x {s,p}`.
   - Over any field where `(-1,-1)_k` splits, such as `F_3`, it embeds unitally in `A_K`.
   - Here `K` is the complete graph on `X x {1,2,3}`.
3. **Commutative form.** `B_X = C_lc({+-1}^X, k) semidirect W`, where `W = F_2 wr_X G`, `G` permutes
   coordinates and the lamp at `x` flips coordinate `x`.

So over `F_3` and the Kun--Thom pair, `A_S <= B_X <= A_K(X x 3)` for every orientable `S`.
- **For counterexamples:** a direct-finiteness failure for any oriented cover already appears in the
  complete-graph skew ring over `X x 3`.
- **For the positive side:** stable finiteness of `B_X` settles every oriented cover at once.

**ESTABLISHED 2026-09-12** by `oriented-clifford-matrix-lamp-embedding-proof`.
