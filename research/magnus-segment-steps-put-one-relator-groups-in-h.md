---
rg: 2
id: magnus-segment-steps-put-one-relator-groups-in-h
kind: claim
title: A twisted Magnus segment step is a root adjunction or a cyclic-edge HNN whose map to Z exists iff the edge functionals survive on the stable window space of the abelianized recurrence, which puts 6 of the 8 open length-11 and 63 of the 73 open length-12 one-relator groups in H
distinct_from:
  edge-injective-quotients-give-hughes-free-division-rings: its root-tower theorem (item 4) is the untwisted root case, where the top letter already forms one syllable and so e_m is nonzero and the window space is everything; this adds the twist a_m = alpha^-1 s beta^-1, the cyclic-HNN segment step with e_m = 0, and the exact window-space test, and it closes relators that item 4 and the retraction rules leave open.
  vertex-injective-quotients-give-hughes-free-division-rings: that needs a map injective on whole vertex groups or a retraction onto an edge group; the segment steps here need only one map to Z per segment, nonzero on one or two edge elements.
  baumslag-gersten-group-is-hughes-free-embeddable: that climbs one ascending HNN of BS(1,2) by retract segments; this climbs Magnus segments of two-generator one-relator groups by root adjunctions and cyclic HNNs.
  unit-alexander-singular-hidden-free-pieces-special: that lane proves virtual specialness and soficity statements for unit-Alexander relators of length 19; this is about Hughes-free division rings, and its two surviving length-11 relators are exactly unit-Alexander ones, where the perfect kernel makes every segment edge element that matters invisible to Z.
  kaplansky-zero-divisor-conjecture: this adds no case of the conjecture; every group in H is locally indicable, so it already satisfies it (Higman 1940; Burns-Hale), and for one-relator groups even the division-ring embedding is classical (Lewin-Lewin 1978).
artifacts:
  - experiments/one-relator-hughes-free-char-p-2026-09-17/segment_certify.py
  - experiments/one-relator-hughes-free-char-p-2026-09-17/words-L11.txt
  - experiments/one-relator-hughes-free-char-p-2026-09-17/census-L12.txt
  - experiments/magnus-hnn-vertex-quotients-2026-09-17/hierarchy_certify.py
---

**ESTABLISHED** (written proof, unreviewed) by [[magnus-segment-steps-put-one-relator-groups-in-h-proof]]. It gives
a new class for Hughes-free existence and a precise obstruction for the two relators that survive. It gives
nothing new for the zero-divisor conjecture (see the last section).

**Setting.** `𝓗` is the class of hereditarily Hughes-free embeddable groups of
[[vertex-injective-quotients-give-hughes-free-division-rings]]. A group is in `𝓗` if every subgroup `Γ` has the
property that every crossed product `E * Γ` over every division ring `E` has a Hughes-free division ring.
- Let `G = <a, t | r>`, where `t` has exponent sum `0` in `r`.
- Let `r' ∈ F(a_0, …, a_m)`, with `m ≥ 1`, be its Magnus rewrite, where `a_i = t^{-i} a t^i`, and let `e_i` be
  the exponent sum of `a_i` in `r'`.
- Put `A = F(a_0, …, a_{m-1})`.
- The *window space* `M_∞ ⊆ Q^m` is the stable term of the decreasing chain `M_0 = Q^m`,
  `M_{L+1} = {(w_1, …, w_m) : ∃ w_0 with (w_0, …, w_{m-1}) ∈ M_L and Σ_i e_i w_i = 0}`.
  So `M_{L+1}` is the set of last-`m`-coordinate windows of rational solutions of `Σ_i e_i x_{j+i} = 0`,
  `0 ≤ j ≤ L - 1`. The chain stabilizes after at most `m + 1` steps.
- For `w ∈ F(A)`, write `c_w ∈ Q^m` for its exponent vector. Read `c_w` as a linear functional on `Q^m`.

## Theorem

1. **Segment-step theorem.** Suppose that for some `α, β ∈ F(A)` the substitution `a_m = α^{-1} σ β^{-1}` turns
   `r'` into a cyclic word of one of these two forms:
   - **(root)** `σ^k u^{-1}` with `u ∈ F(A)` and `k ≠ 0`, where `|k| = 1` or `c_u` does not vanish on `M_∞`;
   - **(hnn)** `σ^{-1} x σ y` with `x, y ∈ F(A)`, where neither `c_x` nor `c_y` vanishes on `M_∞`.

   Then `G ∈ 𝓗`. The same holds with `a_0` in place of `a_m` and indices reversed.

   In either case each Magnus segment `S_[0,n+1]` is `S_[0,n]` with a `k`-th root of `u_{n+1}` adjoined, or an
   HNN extension of `S_[0,n]` along `<x_{n+1}> -> <y_{n+1}^{-1}>`. The window-space condition is equivalent to
   the existence, for every `n`, of a map `S_[0,n] -> Z` that is nonzero on the relevant edge elements.
2. **What is new against item 4 of [[edge-injective-quotients-give-hughes-free-division-rings]].**
   - If `e_m ≠ 0` then `M_∞ = Q^m`, and the root case with `α = β = 1` is exactly that root-tower theorem.
   - The hnn case always has `e_m = 0`, since `σ` has exponent sum `0` in `r'`, and there the window space is
     a proper subspace in general. For example, for `e = (0, 1, 0)` it is the line `{(0, w)}`.
3. **Decisive computation.** `segment_certify.py` adds rule 1, with `|α|, |β| ≤ 2`, to the certifier of
   [[edge-injective-quotients-give-hughes-free-division-rings]], and computes `M_∞` exactly over `Q`.
   - **Length 11.** Six of the 8 relators that census left open are now in `𝓗` (`words-L11.txt`). Each is
     certified by one segment step on the Magnus rewrite of its Nielsen normal form:

     | relator | Magnus rewrite | step |
     |---|---|---|
     | `A A A A B B A b A B B` | `X0X2x1X0X2` | root, `k = 2`, `β = a_0` |
     | `A A A A b b A B A b b` | `x0x2X1x0x2` | root, `k = 2`, `β = a_0` |
     | `A A B a b a B B a a b` | `X0x1X2X0x2` | hnn, `α = β = 1` |
     | `A A B a B A b b a B B` | `X0X2x1X0x2` | hnn, `α = β = 1` |
     | `A A B a a b b a B a b` | `X0x2x0X1x2` | root, `k = 2`, `β = a_0^{-1}` |
     | `A A B a a b A B A b b` | `X0x2X1x0x2` | root, `k = 2`, `β = a_0^{-1}` |

   - **Length 12.** Of the 73 relators left open before (up to rotation, inversion and relabelling), 63 are now
     certified. The 10 left are listed in `census-L12.txt`. So every torsion-free two-generator one-relator
     group with relator of length at most 12 lies in `𝓗`, except 2 at length 11 and 10 at length 12.
   - **All 12 survivors have perfect kernel.** Every one of them has a Nielsen normal form whose Magnus rewrite has
     span 2 and exponent vector `e = (0, ±1, 0)`. So its Alexander polynomial is `±t`, `N` is perfect, and
     `M_∞ = {(0, w)}`. Two of the ten at length 12 have the same normal forms as the two at length 11. The ten
     rewrites are listed in the proof.
4. **Obstruction for the two survivors at length 11.** Take `r_6 = A A B a b a B A A b b` and
   `r_8 = A A B B A A b a B a b`. Their rewrites are `a_0^{-1} a_1 a_2^{-1} a_0 a_2` and
   `a_0^{-1} a_2^{-1} a_0 a_1^{-1} a_2`. Both have `e = (0, ±1, 0)`, so the Alexander polynomial is a unit and
   `N = ker(G -> Z)` is perfect.
   - For every `α, β` of any length, and in both directions, the substituted relator is a cyclic word
     `σ^{-1} x σ y`, and one of `x, y` is conjugate in `F(A)` to `a_0^{±1}`. For example, for `r_6` from the top
     it is `σ^{-1} (α a_0 α^{-1}) σ (β^{-1} a_0^{-1} a_1 β)`.
   - Every map `S_[0,n] -> Z` kills `a_{n+1}`, since the relations force `x_1 = … = x_{n+1} = 0`. So the window
     space is the line `{(0, w)}`, `c_{a_0}` vanishes on it, and rule 1 can never fire, for any twist.
   - The same holds for any climb of these segments by items 2 and 3 of the edge-injective lemma, since both need
     a map to `Z` that is nonzero on the edge element. What is needed is item 5 with a nonabelian target.
5. **The exact HNN criterion.** Let `B ∈ 𝓗` and `x, y ∈ B`. The HNN extension `B *_{σ^{-1} x σ = y}` lies in `𝓗`
   (with `x ≠ 1`) if and only if there are `Q ∈ 𝓗`, a homomorphism `φ: B -> Q` and `τ ∈ Q` such that `φ(x)` has
   infinite order and `τ^{-1} φ(x) τ = φ(y)`. Item 2 of the edge-injective lemma is the case
   `Q = Z[1/d] ⋊ Z`. For `r_6`, the top segment step asks for such a `φ` on `S_[0,n]` with `φ(a_{n+1})`
   conjugate to `φ(a_{n+2}^{-1} a_{n+1})` for every `n`. The obvious candidate is the shift
   `S_[0,n] ≅ S_[-2,n-2] ⊂ S_[-2,n-1]` with `τ = a_{n+1}`, and it is circular, because
   `S_[-2,n-1] ≅ S_[0,n+1]`.

## What is new, and what is not

- **Nothing for the zero-divisor conjecture.** Every group here is a torsion-free one-relator group. Such groups
  are locally indicable (Brodskii, Howie), hence right-orderable (Burns–Hale). So their group rings, and even
  their crossed products, over domains have no zero divisors (Higman 1940), and the group algebras embed in
  division rings (Lewin–Lewin 1978).
- **Hughes-free existence, which is where the content is.**
  - Known before, for group algebras `K[G]`:
    - characteristic `0`, `G` locally indicable (Jaikin-Zapirain and López-Álvarez, with Gräter);
    - every characteristic, `G` virtually compact special (Fisher, Sánchez-Peralta);
    - for all torsion-free one-relator groups in characteristic `p`, open (FSP Question 7.13 for primitivity
      rank 2; Linton and Nyberg-Brodda's survey, §2.4.5).
  - Known before, for crossed products `E * G`: `G` residually (locally indicable and amenable)
    (Jaikin-Zapirain 2021).
  - Rule 1 gives Hughes-free division rings for every crossed product over every division ring, in every
    characteristic, for every relator it certifies, at any length. It uses no hyperbolicity, specialness or
    residual property.
  - I have not decided, relator by relator, which certified groups are also virtually compact special or
    residually (LI amenable). For those that are, only the crossed-product statement is new.
- The census is the calibration of the rule, not the result. The result is the theorem. The census shows that,
  up to length 12, the rule reaches every torsion-free relator except some whose Magnus rewrite has exponent
  vector `(0, ±1, 0)`, that is, except some groups with perfect kernel.

## Where it stops

- **The 2 survivors at length 11 have perfect kernels.** Both have `Δ(t) = ±t`, so `N = G'` is perfect. Any proof
  that they lie in `𝓗` must pass through a nonabelian target `Q ∈ 𝓗` on the segments (item 5).
  - If `Q` is free-by-cyclic, a perfect subgroup maps into the free fiber and so trivially. So the target cannot
    be free-by-cyclic on all of `N`.
  - On the segments, which are not perfect (`H_1(S_[0,n]) = Z^2`, generated by `a_0, a_{n+2}`), no obstruction
    is known.
- **At length 12**, all 10 survivors are again of type `e = (0, ±1, 0)`. Eight of them give groups not among the
  length-11 survivors.
- **Next step.** Find `φ_n: S_[0,n] -> Q` in item 5 uniformly in `n`, for example into a certified one-relator
  group with perfect kernel through a Magnus-compatible map `a ↦ w(a, t)`, `t ↦ t`. Or prove that no
  `Q ∈ 𝓗` works, which would make `r_6` a candidate for a torsion-free one-relator group outside `𝓗`.
