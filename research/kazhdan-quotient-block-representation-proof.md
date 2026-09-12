---
rg: 2
id: kazhdan-quotient-block-representation-proof
kind: route
title: Run the block-invariance steps without the triviality hypothesis, amplify for one direction, take products for the other
target: kazhdan-quotient-sofic-iff-injective-block-representation
requires:
  - kun-expander-decomposition-formalized
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

Error terms are `o(|X_n|)` along `U`. "Most blocks" means all blocks outside a
set of total size `o(|X_n|)`.

**(a) The block representation.** Steps 1--4 of Theorem 6 in the artifact
(Section 7) never use the hypothesis that `Q` has no nontrivial homomorphism
into `S_U`; only Step 5 does.

1. For `s in S`, `g^-1 s g` is a word of bounded length in `S`, so
   `sigma(g)B` is almost `S`-invariant.
2. Almost invariant sets are almost unions of blocks, by the uniform Cheeger
   constant.
3. `sigma(g)B` is an expander for `gSg^-1`, which lies in `N`. So on most
   blocks it almost equals one block `beta_g(B)`, of almost the same size.
4. `beta_(gn) = beta_g` for `n in N`, and `beta_(gh) = beta_g beta_h` on most
   blocks. Order-preserving block maps then define `tau_sigma : Q -> S_U`, a
   homomorphism.

*Well defined up to conjugation.*
- **Choice of edit.** Let `D`, `D'` be two uniform-Cheeger edits. A block of `D`
  has `S`-boundary at most the `o(|X_n|)` edited edges in the graph of `D'`, so
  by step 2 it is almost a union of `D'`-blocks, and symmetrically. So `D` and
  `D'` pair up on all but `o(|X_n|)` points, and the induced block maps agree
  there.
- **Choice of ordering.** Reordering blocks conjugates `tau_sigma` by a blockwise
  permutation.
- **Consequence.** Injectivity and traces of `tau_sigma` do not depend on the
  choices.

**(b), if.** Suppose `tau_sigma` is injective. For `q != 1`,
`tau_sigma(q) != 1` in `S_U`, so its trace is at most `1 - d_q` for some
`d_q > 0` along `U`. Tensor powers `tau_sigma^(otimes k)` have trace at most
`(1 - d_q)^k`. A diagonal choice of `k` over an exhausting sequence of finite
subsets of `Q` gives asymptotic homomorphisms with trace tending to `0` off the
identity. So `Q` is sofic (Elek--Szabo: countable groups embedding in `S_U` are
sofic).

**(b), only if.** Let `rho_n : G -> Sym(X_n)` be a sofic approximation of `G`
and `t_m : Q -> Sym(Y_m)` one of `Q`, with `m = m(n)`. Put

```text
sigma_n(g) = rho_n(g) x t_m(gN)     on X_n x Y_m.
```

- **A sofic approximation of `G`.** `sigma_n` is an asymptotic homomorphism,
  and `tr sigma_n(g) = tr rho_n(g) tr t_m(gN) <= tr rho_n(g) -> 0` for
  `g != 1`.
- **Blocks.** For `s in S`, `sigma_n(s) = rho_n(s) x id`. Taking the Kun edit
  `D` of `rho_n|N` and the product edit `D x {y}` gives a uniform-Cheeger
  decomposition with `o(|X_n||Y_m|)` edits, whose blocks are `B x {y}`.
- **The block map.** `sigma_n(g)(B x {y}) ≈ beta^rho_g(B) x {t(gN)y}`, so
  `tau_sigma(q)` sends block `(B, y)` to `(beta^rho_g(B), t(q)y)`. A point of
  `(B, y)` can be fixed only if `t(q)y = y`. Hence
  `tr tau_sigma(q) <= tr t(q) + o(1) -> 0` for `q != 1`, and `tau_sigma` is
  injective. ∎
