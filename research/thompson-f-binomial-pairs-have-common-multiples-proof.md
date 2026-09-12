---
rg: 2
id: thompson-f-binomial-pairs-have-common-multiples-proof
kind: route
title: No free subgroups plus the relation sequence give a nonzero Fox gradient in the kernel
target: thompson-f-binomial-pairs-have-common-multiples
requires: [thompson-f-has-no-free-subgroups]
---

Notation as in the target. `R = K[F]` has no zero divisors, because `F` is left-orderable
(derivation step 2 of `thompson-f-amenable-iff-group-ring-is-ore`).

**Item 1.** Let `H = <a, c>`, let `Phi` be the free group on letters `alpha, gamma`, let
`pi : Phi -> H` send `alpha -> a`, `gamma -> c`, and let `N = ker pi`.

- *Relation sequence.* Lyndon's relation sequence (K. S. Brown, *Cohomology of Groups*,
  GTM 87, Ch. II §5) is an exact sequence of left `Z[H]`-modules
  `0 -> N/[N,N] -> Z[H]^2 -> Z[H]`. The right-hand map is
  `(u, v) -> u (a - 1) + v (c - 1)`, and the left-hand map sends `r` in `N` to its Fox
  gradient `(dr/d alpha, dr/d gamma)` evaluated in `Z[H]`.
- *Tensor with `K`.* All modules in the sequence are free abelian (`N` is free by
  Nielsen--Schreier), so `Tor_1^Z(-, K)` vanishes on every module involved. The
  sequence therefore stays exact after `⊗_Z K`.
- *`N ≠ 1`.* If `N = 1` then `H` is free on `{a, c}`. That is impossible: a free
  subgroup of rank 2 contradicts `thompson-f-has-no-free-subgroups`, and a cyclic `H`,
  or `a = c^{+-1}`, is not free on two letters.
- *A nonzero kernel element.* `N/[N,N]` is a nonzero free abelian group. A basis element
  `r` has nonzero image in `(N/[N,N]) ⊗ K`, so its Fox gradient `(u, v)` is nonzero in
  `K[H]^2`, and `u (a - 1) + v (c - 1) = 0`.
- *`u ≠ 0`.* If `u = 0`, then `v (c - 1) = 0` gives `v = 0`, since `c ≠ 1` and `R` is a
  domain. That contradicts `(u, v) ≠ 0`. So `u (1 - a) = (-v)(1 - c)` is a nonzero
  common left multiple.
- *Right multiples.* The anti-automorphism `*`, `g -> g^-1`, maps left ideals `R x` to
  right ideals `x* R`. It sends the equation to `(1 - a^-1) u* = (1 - c^-1)(-v)*`, which
  is nonzero. Since `1 - a^-1 = (1 - a)(-a^-1)`, `(1 - a^-1) R = (1 - a) R`, and
  likewise for `c`. So `(1 - a) R ∩ (1 - c) R ≠ 0`.

**Item 2.** For `t` in `supp b`, `t (1 - t^-1 h t) = t - h t = (1 - h) t`, so
`t (1 - t^-1 h t) R ⊆ (1 - h) R`. If `v` lies in `(1 - t^-1 h t) R` for every `t` in
`supp b`, then `b v = sum_t b_t t v` lies in `(1 - h) R`.

**Item 3.**
- *Single element.* If `supp b = {t}`, take `v = 1 - t^-1 h t`, which is nonzero because
  `h ≠ 1`.
- *Two elements.* If `supp b = {t_1, t_2}`, the conjugates `g_i = t_i^-1 h t_i` are
  nontrivial. Item 1 gives a nonzero `v` in `(1 - g_1) R ∩ (1 - g_2) R`. By item 2,
  `b v` is in `(1 - h) R`, and `b v ≠ 0` because `R` is a domain.

**Trust surfaces.** Brin--Squier (`thompson-f-has-no-free-subgroups`), left-orderability
of `F`, and Lyndon's relation sequence are quoted, not re-proved. Everything else is
proved above.
