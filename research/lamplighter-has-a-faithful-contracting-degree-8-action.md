---
rg: 2
id: lamplighter-has-a-faithful-contracting-degree-8-action
kind: claim
title: Z/2 wr Z has a faithful contracting self-similar action on the 8-regular tree, from the virtual endomorphism x^2 -> x, (1+t^2)A(t^2) + t(1+t^2)B(t^2) -> (1+t)A(t); ADT Example 4.8 leaves this map undefined on half of H and wrongly calls it injective
distinct_from:
  rn-groups-of-affine-lamplighters-f-q-wr-z-are-fp: that is the non-contracting affine action on the binary tree, where V is f.p. through lift ideals; this is a different, contracting action on the 8-regular tree, where V is f.p. by Nekrashevych's theorem.
  rover-nekrashevych-finite-presentation-criteria: that imports the contracting criterion FP2; this supplies a contracting action of a group that is not finitely presented, and checks the source that claimed one.
---

**ESTABLISHED (proof in `lamplighter-has-a-faithful-contracting-degree-8-action-proof`; unreviewed).** This is a
check of Almeida–Dantas–Oliveira-Tosti, arXiv:2609.01868, Example 4.8, requested by the
`rn-groups-of-affine-lamplighters-f-q-wr-z-are-fp` lane.

## Setting

`G = Z/2 ≀ Z = F_2[t^{±1}] ⋊ t^Z`, where `b = (1, 0)` is the lamp and `x = (0, t)` is the shift. Put `s = t^2`,
`M = (1+s) F_2[t^{±1}]` and `H = M ⋊ ⟨s⟩`, a subgroup of index `8`. In ADT's notation `M = ⟨[b, x^2]⟩^{⟨x⟩}`,
because `[b, x^2] ↦ 1 + t^2`.

Every `m in M` is uniquely `m = (1+s)A(s) + t(1+s)B(s)` with `A, B in F_2[s^{±1}]`. For `c in F_2[t^{±1}]` define

`f_c: H -> G`, `f_c(m, s^j) = ((1+t)A(t) + c B(t), t^j)`.

Every homomorphism `H -> G` with `[b, x^2] ↦ [b, x]` and `x^2 ↦ x` is some `f_c`, with `c` the image of
`x[b, x^2]x^{-1}`.

## Statement

1. **`f_0` gives a faithful, contracting, finite-state self-similar action of `Z/2 ≀ Z` on the 8-regular tree.**
   With the transversal `{(a, t^e) : a in {0, 1, t, 1+t}, e in {0, 1}}`, each section of `g = (p, t^k)` has
   "radius" at most `(r(g) + 1)/2`, where `r(g)` is the largest of `|k|` and the `|exponents|` of `p`. So the nucleus
   lies in `{r <= 1}`, a finite set. The computed nucleus has 6 elements.
2. **Consequence.** `V_8(Z/2 ≀ Z)` for this action is finitely presented (Nekrashevych, FP2 in
   `rover-nekrashevych-finite-presentation-criteria`), and its commutator subgroup is simple.
3. **What is wrong in ADT Example 4.8.**
   - The example says `f` "extends the map `[b, x^2] ↦ [b, x]`, `x^2 ↦ x`". That map does not determine `f`: `H` needs
     the extra generator `x[b, x^2]x^{-1}`, whose image `c` is free. If `H` is instead read as
     `⟨[b, x^2], x^2⟩`, then `H` has infinite index, and `f` is not a virtual endomorphism.
   - The example then says "as `f` is a monomorphism". No `f_c` is injective. The element
     `(1+s)c(s) + t(1+s)^2` of `M` is nonzero and lies in `ker f_c`.
   - The conclusion that `Z/2 ≀ Z` has a faithful contracting self-similar representation of degree 8 is
     nevertheless true, by (1) with `c = 0`.
   - The step to `Z/2 ≀ (Z/2 ≀ Z)` through their Theorems A and C was not checked here. It cites the false
     injectivity.
4. **Numerics for other `c`.** `experiments/rn-lamplighter-finiteness-2026-09-17/adt48.py` covers every `c` supported
   in `[-2, 2]` with at most 2 terms. In each case the automaton is finite, the computed nucleus is finite (6 to 208
   states), and no kernel element has lamps in `[-3, 3]` and `|shift| <= 1`. Random-path tests (`rand48.py`) show section sizes halving
   level by level. See `results-adt48.txt`.

## Bearing on the lane

- The affine action of `rn-groups-of-affine-lamplighters-f-q-wr-z-are-fp` is still non-contracting, and its
  f.p. result is still new for that action.
- The group `Z/2 ≀ Z` itself already has a Röver–Nekrashevych group that is finitely presented through a contracting
  action.
- Whether `V_2(Z/2 ≀ Z)` (affine, binary) and `V_8(Z/2 ≀ Z)` (this action) are isomorphic is open.
