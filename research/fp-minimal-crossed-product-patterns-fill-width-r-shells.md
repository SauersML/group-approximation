---
rg: 2
id: fp-minimal-crossed-product-patterns-fill-width-r-shells
kind: claim
title: For a finitely presented crossed product of an infinite minimal subshift of SFT radius r, two points agreeing on the width-r shell N_r(F) minus F agree on F, so pattern counts are bounded by the width-r shell and not only by the width-2r one
distinct_from:
  fp-minimal-crossed-products-have-no-homoclinic-pairs: that is the qualitative statement whose item 2 asserts exactly this width; its route derives item 2 by splicing on the width-r shell, which is the step this claim supplies.
  fp-minimal-crossed-products-have-shell-bounded-complexity: that is the counting consequence whose part 1 has the width-r exponent; parts 2 to 4 need only a shell of some fixed width and survive at width 2r.
  fp-crossed-products-force-connected-differences: that establishes the same rigidity at width 2r, with the layer taken as the inner boundary {p in F : p B_{2r} not contained in F}; this asks for the factor-two improvement to width r, which is strictly stronger and is not proved there.
  fp-crossed-products-force-sft-over-any-group: that supplies the SFT radius r itself, by forbidding r-ball patterns; this is a statement about how far an r-window reaches past a set it meets.
artifacts:
  - research/artifacts/fp-minimal-crossed-products-homoclinic-kill-2026-09-17.md
---

**OPEN.**

## Statement

Let `P` be a finitely generated group with the word metric of a finite symmetric generating
set, `B_w` the ball of radius `w`, and `N_w(F) = F B_w`. Let `A` be a finite alphabet,
`X ⊆ A^P` an infinite minimal subshift, `k` a field, and suppose `LC(X,k) ⋊ P` is finitely
presented, so that `X` is an SFT of some radius `r` (`fp-crossed-products-force-sft-over-any-group`:
`X` is defined by forbidding the patterns on balls `p B_r`). Then for every finite `F ⊆ P`:

1. Any two points of `X` that agree on the shell `N_r(F) \ F` agree on `F`.
2. Consequently `|L_F(X)| <= |A|^{|N_r(F) \ F|}`.

## Why the splice argument does not give this width

The route for `fp-minimal-crossed-products-have-no-homoclinic-pairs` gets item 1 from the
splice "let `z` be `y` on `F` and `x` elsewhere; its windows meeting `F` lie in `N_r(F)`,
where `z = y`, so `z ∈ X`". That containment is false. A window is `y|_{p B_r}`; if
`p B_r` meets `F` at some `f` then `f ∈ p B_r`, hence `p ∈ f B_r`, hence `p B_r ⊆ f B_{2r}`,
i.e. the window lies in `N_{2r}(F)` and not in `N_r(F)`. The containment is sharp: take
`F = {f}` and `p` at distance exactly `r` from `f`; the window reaches distance `2r` from `f`.
So with `x = y` only on `N_r(F) \ F`, the spliced point `z` is a mix of `x` and `y` on the
windows poking into `N_{2r}(F) \ N_r(F)`, those window patterns need not lie in `L_{B_r}(X)`,
and `z` need not lie in `X`.

The artifact itself gets the geometry right 25 lines earlier: Theorem 2, step 4 says of a
window meeting `D_0` that "it lies in `N_{2r}(D_0) = K`", and sets `K = N_{2r}(D_0)` for
exactly this reason. Corollary 3 then writes `N_r` for the identical situation.

**The general principle invoked at radius `r` is false.** The period-4 orbit of `(0011)^∞`
in `{0,1}^Z` is a minimal SFT of window radius `r = 1` (allowed 3-blocks `001, 011, 110, 100`;
the follower graph is a single 4-cycle, so the SFT is exactly that 4-point orbit) with no
homoclinic pairs, yet the two points with shell `(x(-1), x(1)) = (0, 1)` differ at `0`. At
`2r = 2` the collision disappears. So this claim, if true, is not a consequence of the SFT
radius and the absence of homoclinic pairs alone: it needs finite presentation of the crossed
product to enter again, at width `r`.

## What is known at width 2r

Everything the splice argument actually proves:

- Two points agreeing on `N_{2r}(F) \ F` agree on `F`, hence `|L_F(X)| <= |A|^{|N_{2r}(F) \ F|}`.
- Independently, `fp-crossed-products-force-connected-differences` (ESTABLISHED) states the
  same rigidity with the layer taken at width `2r`.

Both suffice for every downstream corollary that needs only a shell of *some* fixed width:
zero entropy over amenable `P`, impossibility over virtually cyclic `P`, and
`log|L_{B_N}(X)| <= C N^{d-1}` over `Z^d`.

## Attempts

- 2026-09-18 (referee pass on `fp-minimal-crossed-products-have-no-homoclinic-pairs` and
  `fp-minimal-crossed-products-have-shell-bounded-complexity`): recorded as the gap, with the
  sharpness example and the `(0011)^∞` counterexample to the general principle. No attempt to
  recover width `r` from finite presentation.
