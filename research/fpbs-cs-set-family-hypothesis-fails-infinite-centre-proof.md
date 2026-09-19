---
rg: 2
id: fpbs-cs-set-family-hypothesis-fails-infinite-centre-proof
kind: route
title: A disjoint short translate of a supporting set forces a conjugate outside A A^-1, and central elements have bounded conjugates
target: fpbs-cs-set-family-hypothesis-fails-infinite-centre
requires: []
artifacts:
  - research/artifacts/fpbs-acylindrical-l2-gap-2026-09-16.md
  - experiments/fpbs-conjugation-expansion-2026-09-17/check_conjugation_expansion.py
  - experiments/fpbs-conjugation-expansion-2026-09-17/output.txt
---

This proof is complete and self-contained. It uses only the *statement* of
Choi–Seo `thm:hutchcroft1plus2`, quoted verbatim in the target from the TeX
source (artifact, CS4). It does not use the truth of that theorem or anything
from its proof. The notation is that of the target. `B(R)` is the closed
ball of radius `R` about `e` in the word metric `||.||_S`, so `e ∈ B(R)`.

## Step 1. Part (a): the necessary condition

Fix a family `𝓗`, a radius `R`, a finite set `A` and a point `a ∈ A`. Suppose
some `g, h` with `||g||_S, ||h||_S <= R` satisfy

```text
A ⊆ a H(g)        and        H(g) ∩ h H(g) = ∅ .
```

Then `a^-1 A ⊆ H(g)` and `h a^-1 A ⊆ h H(g)`. Since `H(g)` and `h H(g)` are
disjoint, so are `a^-1 A` and `h a^-1 A`.

Now suppose, for contradiction, that `a h a^-1 = x y^-1` for some
`x, y ∈ A`. Then `a^-1 x = h a^-1 y`. This element lies in `a^-1 A`, and also
in `h a^-1 A`, which contradicts disjointness. So `a h a^-1 ∉ A A^-1`, and
`h ∈ B(R)`.

If SF(𝓗,R) holds, the set `A'` it provides has `#A' >= #A/2`, and every
`a ∈ A'` is therefore **good**: some `h ∈ B(R)` has `a h a^-1 ∉ A A^-1`.
This proves (a).

Since `a e a^-1 = e = a a^-1 ∈ A A^-1`, the element `h` of a good point is
never `e`. This is not needed below.

## Step 2. Part (b): the conjugation-expansion test

Let `E` be finite and nonempty with `#(D_R(E) \ E) < #E`. Put
`A = E ∪ D_R(E)`.

*Every point of `E` is bad.* Take `a ∈ E` and `h ∈ B(R)`. Then
`a h a^-1 ∈ D_R(E) ⊆ A` by definition. Also `e = a e a^-1 ∈ D_R(E) ⊆ A`,
because `e ∈ B(R)`. So

```text
a h a^-1 = (a h a^-1) · e^-1 ∈ A A^-1 .
```

This holds for every `h ∈ B(R)`, so `a` is not good.

*Counting.* The good points lie in `A \ E = D_R(E) \ E`. Also
`#A = #E + #(D_R(E) \ E)`. Hence

```text
#good <= #(D_R(E) \ E) < (#E + #(D_R(E) \ E)) / 2 = #A / 2 ,
```

where the strict inequality is exactly the hypothesis `#(D_R(E) \ E) < #E`.
By (a), no family `𝓗` can satisfy SF(𝓗,R), because SF would provide at least
`#A/2` good points. This proves (b).

## Step 3. Part (c): infinite centre

Let `Z(G)` be infinite, and fix `S`, `R > 0` and `𝓗`. `B(R)` is finite, since
`S` is finite. Choose `F ⊆ Z(G)` with `#F > #B(R)`. For `f ∈ F` and
`h ∈ B(R)`, `f h f^-1 = h`, so `D_R(F) = B(R)`. Then

```text
#(D_R(F) \ F) <= #B(R) < #F ,
```

and (b) applies with `E = F`. The witness is `A = F ∪ B(R)`. So SF(𝓗,R) fails
for every `𝓗` and every `R`, and the hypothesis of `thm:hutchcroft1plus2` is
never satisfied on `Cay(G,S)`. This proves (c). QED.

## Step 4. Machine check

`check_conjugation_expansion.py` builds `A = E ∪ D_R(E)` on `F_2 x Z` for two
generating sets, with `E` a set of `#B(R) + 2` central elements:
* the product set `{(a,0),(b,0),(e,1)}`;
* the non-product set `{(a,1),(b,0),(a,0)}`.

For `R = 1, 2, 3` it tests every `h ∈ B(R)` for every point, by brute force.
In all six cases fewer than half of the points of `A` are good. For example,
with the non-product set at `R = 3`, 114 of 262 points are good. On
`F_2 = Cay(F_2, free basis)` (acylindrically hyperbolic, where [CS] verify
SF), the ratio `#(D_R(E) \ E)/#E` stayed `>= 1.8` on 202 test sets. That is
consistent with (b) being sharp in that direction. See `output.txt`.

## Step 5. Why central fibres are the obstruction

In `F_2 x Z` take the witness `A = F ∪ B(R)` with `F = {z^0, ..., z^(M-1)}` a
long central segment, and base point `a = z^k ∈ F`. Then `a^-1 A` contains
`z^-k B(R)`, a ball about `z^-k`. For each short `h`, the translate
`h a^-1 A` contains `h z^-k = z^-k h`, which lies in that ball.

So any `H(g)` containing `a^-1 A` meets `h H(g)`, for every short `h`. The
central base points outnumber the rest of `A`. The ball `B(R)`, a bounded set,
is enough to pin all of them, because conjugation by a central element carries
the ball onto itself.

In an acylindrically hyperbolic group, WPD makes long segments along loxodromic
axes separable by short translations: `prop:supportingWPD` uses this.
Centrality is the extreme failure of WPD. The centralizer of the whole
generating ball is infinite, so conjugation by `E` never spreads `B(R)`.
