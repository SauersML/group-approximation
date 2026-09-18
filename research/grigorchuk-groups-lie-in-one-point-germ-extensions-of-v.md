---
rg: 2
id: grigorchuk-groups-lie-in-one-point-germ-extensions-of-v
kind: claim
title: Every Grigorchuk group G_omega lies in the finite germ extension <V, b_omega, c_omega, d_omega> of Thompson's V, with one singular orbit and germ group W_omega x| Z; the germ group is finitely presented exactly when omega is eventually periodic
distinct_from:
  eventually-periodic-grigorchuk-groups-satisfy-boone-higman: that settles eventually periodic omega through contracting self-similar hosts; this gives one explicit host for every omega and locates exactly where finite presentation fails.
  bhm-singfix-condition-forces-fp-germ-groups: that is the general lemma that Belk-Hyde-Matucci's Theorem 2.1 needs finitely presented germ groups; this computes the germ group for Grigorchuk hosts.
---

**ESTABLISHED** (lane proof below, elementary apart from the cited Bieri–Strebel theorem; not
reviewed; no novelty claimed).

## Statement

Use the notation of `eventually-periodic-grigorchuk-groups-satisfy-boone-higman`. Let `V` act on
`{0,1}^N` and `p = 1^∞`. Put `E_ω = ⟨V, b_ω, c_ω, d_ω⟩`. Then:

1. `G_ω <= E_ω`, and `E_ω` is a finite germ extension of `V` (Belk–Hyde–Matucci, arXiv:2407.03149)
   whose singular points form the single orbit `V·p`.
2. The germ group of `E_ω` at `p` is `Γ_ω = W_ω ⋊ ⟨t⟩`, where
   - `t` is the germ at `p` of the element of `V` sending `1x -> 11x` near `p`;
   - `W_ω` is the `F_2[t^±]`-submodule of `P(N)/fin` spanned by the classes of
     `A_s = {k : u^s_(ω_k) = a}`, `s ∈ {b,c}`, with `t` acting by `A -> A + 1`.
3. `W_ω` is finite exactly when `ω` is eventually periodic. When `ω` is not eventually periodic,
   `Γ_ω` is not finitely presented.
4. So for `ω` not eventually periodic, Belk–Hyde–Matucci's Theorem 2.1 cannot certify `E_ω`
   finitely presented, by `bhm-singfix-condition-forces-fp-germ-groups`.

`E_ω` is finitely generated, since `V` is, and has solvable word problem when `ω` is computable,
because the action of each generator on finite words is computable.

## Proof

1. `a ∈ V`. On each cylinder `1^k 0 {0,1}^N`, `s_ω` is either the identity or the prefix swap
   `1^k 0 0 y <-> 1^k 0 1 y`. So `s_ω` agrees with an element of `V` near every point except `p`, and
   it fixes `p`. Near `p` it is not locally a single prefix replacement unless `A_s` is finite or
   cofinite. So the generators are `V`-local away from `p`, and the singular set of `E_ω` is `V·p`.
2. An element of `E_ω` fixing `p` is a word in `V ∪ {b_ω, c_ω, d_ω}`. Follow `p` through the word: each
   letter from `V` moves the current point within `V·p` by a `V`-germ, and each letter from
   `{b,c,d}` acts at the current point by a `V`-germ unless that point is `p`, where it acts by the
   germ `f_(A_s)`. The germs of `V`-elements that fix `p` form `⟨t⟩`. Conjugating,
   `t^-1 f_A t = f_(A ± 1)`, with the sign fixed by convention. So the germ group at `p` is generated
   by `t` and the germs `[f_(A_b)]`, `[f_(A_c)]`. Maps `f_A` commute and are involutions, and
   `[f_A] = [f_(A')]` exactly when `A △ A'` is finite. So the germ group is `W_ω ⋊ ⟨t⟩` as stated.
   (`A_d = A_b △ A_c`, because `d = bc`.)
3. The pair `(A_b, A_c)` determines `ω`: the three values of `ω_k` give the three distinct patterns of
   membership. A class `[A]` is `F_2[t]`-torsion exactly when some nonzero `f(t)` kills `A` up to
   finitely many terms, i.e. when the indicator sequence satisfies a linear recurrence over `F_2`
   from some point on. That happens exactly when `A` is eventually periodic. So `W_ω` is finite iff
   `A_b` and `A_c` are eventually periodic iff `ω` is.
   Suppose `W_ω` is infinite and `Γ_ω` is finitely presented. The kernel `W_ω` of `Γ_ω -> Z` is
   abelian, so it contains no free subgroup of rank 2. By Bieri–Strebel (Math. Z. 1978; not re-read),
   `Γ_ω` is then an ascending HNN extension over a finitely generated base `B <= W_ω`. `B` is finite,
   being a finitely generated abelian group of exponent 2, so `t B t^-1 <= B` forces equality and
   `W_ω = ∪_n t^n B t^-n = B`, a contradiction.
4. is the cited lemma: Theorem 2.1's hypothesis at `n = 2` includes the one-point `SingFix` group,
   whose finite presentation forces the germ group to be finitely presented.

## What stays open

Whether `E_ω`, or some other host, is finitely presented for computable `ω` that is not eventually
periodic. Enlarging the germ group to a finitely presented metabelian group containing `W_ω ⋊ Z`,
in the style of Baumslag's embedding of `Z/2 ≀ Z`, needs a homeomorphism near `p` whose germ acts
on `W_ω` invertibly. For example, multiplication by `1+t` kills the class of `N`, so it is invertible
on `W_ω` only when `[N] ∉ W_ω`. This is recorded, not attempted.
