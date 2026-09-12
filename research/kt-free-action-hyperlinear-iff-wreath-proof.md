---
rg: 2
id: kt-free-action-hyperlinear-iff-wreath-proof
kind: route
title: Fourier-transform the free action into a generalized wreath over W acting on G through its quotient, then apply GKP Theorem 3.8
target: kt-free-action-hyperlinear-iff-wreath-hyperlinear
requires:
  - gkp-connes-embeddable-generalized-wreath-permanence
  - gkp-sofic-action-toolkit
---

# Proof

**Step 1, the crossed product is a group algebra.** Put `I = G/Γ ⊔ G` with the
left action of `G`. Fourier transform identifies `L(⊕_I Z/2)` with
`L^∞(({0,1},fair)^I)` (the dual of `⊕_I Z/2` is `{0,1}^I` with Haar measure the
fair product measure), equivariantly for the permutation action of `G`. So

```text
L^∞(X) ⋊ G  ≅  L(⊕_I Z/2) ⋊ G  =  L( (⊕_I Z/2) ⋊ G )  =:  L(W'),
```

and item 1 is hyperlinearity of `W'` (a group is hyperlinear iff its group von
Neumann algebra is Connes-embeddable). Item 2 is the same algebra, since `X` is
free.

**Step 2, `W'` contains `W`.** `(⊕_(G/Γ) Z/2) ⋊ G <= (⊕_I Z/2) ⋊ G`, and
subgroups of hyperlinear groups are hyperlinear. So 1 implies 3.

**Step 3, `W'` is a generalized wreath over `W`.** The two lamp blocks commute
and `⊕_(G/Γ) Z/2` acts trivially on `⊕_G Z/2`, so

```text
W' = (⊕_G Z/2 ⊕ ⊕_(G/Γ) Z/2) ⋊ G  =  (⊕_G Z/2) ⋊ W  =  Z/2 ≀_α W,
```

where `α : W ↷ G` is left translation through the quotient `p : W → G`.

**Step 4, `α` is a sofic set action.** `G` is residually finite, hence sofic, so
its left-regular action `G ↷ G/{1}` is sofic (GKP Theorem 2.14 with `N = {1}`,
in `gkp-sofic-action-toolkit`). Precompose with `p`. If `ψ : G → Sym(A)` is unital,
`(p(F),ε)`-multiplicative and a `(p(F),E,ε)`-orbit approximation of the regular
action, then `φ = ψ ∘ p` is unital and `(F,ε)`-multiplicative, and it is an
`(F,E,ε)`-orbit approximation of `α`, because the orbit condition
`π_(φ(w)s)(x) = π_s(α(w^(-1))x)` involves `w` only through `p(w)`. GKP Definition
2.1(5) has no separation clause, so `α` is sofic. (This is GKP Proposition
2.15(1), transcribed in `research/artifacts/gkp-2401-04945-verified.md`.)

**Step 5, 3 implies 1.** If `W` is hyperlinear, GKP Theorem 3.8
(`gkp-connes-embeddable-generalized-wreath-permanence`) with lamp group `Z/2`,
acting group `W` and the sofic action `α` makes `Z/2 ≀_α W = W'` hyperlinear.

**Step 6, factors.** If a `G`-action `X'` has the generalized Bernoulli action
`Y = ({0,1},fair)^(G/Γ)` as a factor, then `L^∞(Y) ⋊ G = L(W)` embeds
trace-preservingly in `L^∞(X') ⋊ G` (Lemma A of
`sofic-action-class-commensurability-proof`). So hyperlinearity of `X'` forces
hyperlinearity of `W`, which is the "no cheaper" remark in the claim.
