---
rg: 2
id: heisenberg-group-embeds-in-wobbling-group-of-some-zn-proof
kind: route
title: A snowflake embedding rounds to a Lipschitz injection of the Cayley graph into Z^N, which conjugates right multiplication into W(Z^N)
target: heisenberg-group-embeds-in-wobbling-group-of-some-zn
requires:
  - doubling-snowflakes-embed-bilipschitz-in-rn
---

`H = H_3(Z)` carries the left-invariant word metric `d_w` for
`{a^{±1}, b^{±1}}`. Norms on `Z^N` are `ℓ^1` unless marked.

1. **Doubling.** `|B_w(r)|` lies between `c r^4` and `C r^4` for `r ≥ 1`
   (Bass–Guivarc'h; for `H_3(Z)` this follows from the normal form
   `a^x b^y c^s` with `|x|, |y| ≤ r` and `|s| ≤ r^2`, together with
   `c^{p^2} = [a^p, b^p]`). Let `P` be a maximal `r`-separated subset of
   `B_w(x, 2r)`. The balls `B_w(p, r/2)` are disjoint and lie in
   `B_w(x, 3r)`, so `|P| ≤ C(3r)^4 / (c (r/2)^4)` for `r ≥ 2`. Balls with
   `r < 2` have at most `|B_w(4)|` points. So `(H, d_w)` is doubling, and it is
   countable, hence separable.
2. **Snowflake.** Apply `doubling-snowflakes-embed-bilipschitz-in-rn`
   with `ε = 1/4`. It gives `ψ : H → R^N` and `s > 0` with
   `s d_w^{3/4} ≤ |ψ(g) − ψ(g')|_2 ≤ D s d_w^{3/4}`. Replace `ψ` by
   `(2√N/s) ψ`. Distinct points have `d_w ≥ 1`, so
   `|ψ(g) − ψ(g')|_2 ≥ 2√N` for `g ≠ g'`, and
   `|ψ(g) − ψ(g')|_2 ≤ 2√N D d_w(g,g')`, using `d_w^{3/4} ≤ d_w`.
3. **Rounding.** Let `ι(g) ∈ Z^N` be a nearest lattice point to `ψ(g)`, so
   `|ι(g) − ψ(g)|_2 ≤ √N/2`.
   - `ι` is injective: two distinct points of `H` have images at distance
     `≥ 2√N − √N > 0`.
   - `ι` is Lipschitz: `|ι(g) − ι(g')|_1 ≤ √N(2√N D d_w + √N) ≤ 3ND·d_w`
     for `g ≠ g'`.
4. **Host.** `H` acts faithfully on itself by `R_h(x) = x h^{-1}`, with
   `d_w(x, R_h x) = |h|_w`.
   - Define `ĥ = ι R_h ι^{-1}` on `ι(H)`, and the identity on `Z^N ∖ ι(H)`.
   - Each `ĥ` is a bijection of `Z^N`, and `h ↦ ĥ` is an injective
     homomorphism.
   - `|ĥ(z) − z|_1 ≤ 3ND|h|_w` for all `z`, so `ĥ ∈ W(Z^N)`. ∎

**Remark (sketch, not used).** Consider a Lipschitz injection
`Cay(H) → Z^N`. Rerunning §5 of `heisenberg-not-in-full-groups-of-z3-actions-pansu-proof`
with fibres of size 1 compares a lower count `~(rj)^4` with an upper count
`~(rj)^2(εrj + 1)^{N−2}`. This suggests `N ≥ 5` for embeddings of this kind.
A faithful `H`-set other than `H` itself might still fit in `Z^4`. Whether
`H ≤ W(Z^4)` is not decided here.
