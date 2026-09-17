---
rg: 2
id: poly-growth-cantor-hosts-need-exponential-complexity
kind: claim
title: Over an acting group of polynomial growth, a Cantor crossed product hosts only group algebras of subexponential-growth groups unless its ball pattern count is exponential in the radius, and at polynomial complexity (Labbé's shift) only virtually nilpotent ones
distinct_from:
  positive-entropy-sft-crossed-products-are-not-fp: that kills positive entropy at finite presentation; this kills the opposite end, complexity below e^(cN) in the radius N, at the embedding of F_2[F_2]. Over Z^d with d >= 2 zero entropy allows up to e^(o(N^d)), so the two leave a band between them.
  free-group-cantor-crossed-products-are-not-universal-hosts: that kills free acting groups by word-problem complexity; this kills low-complexity spaces over polynomial-growth acting groups by growth, with no finite presentation or finite type hypothesis.
  subexponential-complexity-zd-subshift-rings-have-rank-models: that uses subexponential complexity to build rank models, a positive feature for the ring route; this shows the same hypothesis makes the host useless for exponential-growth inputs on the crossed-host route.
  labbe-wang-shift-crossed-product-is-finitely-presented: that is the open finite presentation gate for Labbé's host; this shows that, whatever that gate's answer, Labbé's host contains no group algebra of a non-virtually-nilpotent group.
---

**ESTABLISHED (unreviewed).** Let `k` be a field and `P` a finitely generated group with polynomial growth,
`|B_P(N)| <= C N^D` for `N >= 1`. Let `X` be a `P`-subshift and put `λ_X(N) = |L_(B_P(N))(X)|`. Let `G` be a
finitely generated group with an injective algebra homomorphism `k[G] -> LC(X, k) ⋊ P` (unital or not).

1. **Linear-exponential complexity is needed.** If `G` has exponential growth, with
   `ω_G = lim_n |B_G(n)|^(1/n) > 1` for some generating set, then for some `m >= 1` (depending on the embedding)
   `liminf_N (log λ_X(N)) / N >= (log ω_G) / m > 0`. Equivalently, if `liminf_N (log λ_X(N)) / N = 0`, every
   hosted group has subexponential growth. In particular `k[F_2]` embeds in no such host.
2. **Polynomial complexity gives only virtually nilpotent inputs.** If `λ_X(N) <= C' N^E` for `N >= 1`, then `G`
   has polynomial growth, hence is virtually nilpotent.
3. **Labbé's host.** For Labbé's aperiodic Wang shift `Ω_U` over `P = Z^2`, the only finitely generated groups
   `G` with `k[G] ↪ LC(Ω_U, k) ⋊ Z^2` are virtually nilpotent. So, whether or not
   `labbe-wang-shift-crossed-product-is-finitely-presented` holds, this host is not a witness for
   `decidable-group-algebras-have-fp-cantor-crossed-hosts` at input `F_2`.
4. **Full-group subgroups.** Parts 1 and 2 also apply when the action is topologically free, to every finitely
   generated `G ≤ F(P ⋉ X)` in which each `g ≠ e` has a fixed-point set with empty interior
   (`crossed-product-growth-bounded-by-ball-patterns`, part 3).

For a general compact totally disconnected `X`, parts 1 and 2 apply to the subshift factor carrying the
coefficients of the embedding (Remark in the growth-bound node).

**Class killed.** Crossed-host witnesses `(P, X)` with `P` of polynomial growth (torsion-free nilpotent `P` are
Farrell–Jones and admissible for the target) and `X` of complexity `e^(o(N))` in the radius. This covers every
polynomial-complexity shift, in particular substitutive shifts with polynomial pattern count such as Labbé's.
- **Invariant.** The pattern count `λ_X(mn + r)` bounds the span of degree-`n` products.
- **Failing step.** The embedding `k[F_2] -> B`, independent of finite presentation, simplicity and the
  word-problem complexity of the input.

**What escapes.**
- `P` of exponential growth.
- `X` with `log λ_X(N) >= cN`.
- Tensor products with boundary factors, e.g. `LC(Ω × ∂F_d) ⋊ (Z^2 × F_d)`, which have exponential growth.
  Their finite presentation forces that of the `Z^2` factor by `tensor-product-algebra-fp-iff-factors-fp`.
- The units-only version. Route step 1 of `boone-higman-via-central-simple-leavitt-tensor-host` uses only
  `G ≤ B^x`, and the group elements need not be linearly independent there. A unit group of a
  polynomial-growth algebra can contain `F_2`, e.g. `GL_2(F_2[t])` (Nagao's amalgam, recalled, not load-bearing).
  So in this class an input must be realized by non-permutational units or by elements with fat fixed-point sets.

Route: `poly-growth-cantor-hosts-need-exponential-complexity-proof`.
