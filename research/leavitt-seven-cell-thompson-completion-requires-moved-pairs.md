---
rg: 2
id: leavitt-seven-cell-thompson-completion-requires-moved-pairs
kind: claim
title: A seven-cell Thompson completion must move paired cells and have a noninvolutive compiled p1
distinct_from:
  leavitt-finite-wreath-targets-have-eight-tail-normal-form: That gives an equivalent eight-tail problem for all finite Thompson-wreath witnesses; this fixes a particular seven-cell finite core and diagonal Thompson copy, giving a sufficient one-equation construction and an obstruction within it.
  leavitt-packet-kernel-is-normally-generated-by-each-cycle: That proves every nontrivial image retains all eight local Thompson copies; this gives a particular finite-core completion equation and a moved-region obstruction without constructing such an image.
artifacts:
  - research/artifacts/leavitt-seven-cell-centralizer-completion-2026-09-08.md
  - experiments/leavitt_seven_cell_exact_replay.py
---

There is an explicit seven-cell action of `SL_3(F_2)` in `V`, with
marked cycle `C` and involution `Y`, and an explicit diagonal copy of
`V` sharing its compiled generators `A,C,D`. Write `B_0` for the
second generator of this diagonal copy. An involution `Z` commuting
with `Y` and satisfying

```text
B(C,Y,Y,Z)=B_0
```

would give a homomorphism from the exact eight-word quotient `Q` to
`V` retaining `c`. This is a sufficient condition for this particular
construction, not an equivalent replacement for all maps `Q->V`.

Every such `Z` must act nontrivially on the region moved by `Y`.
An involution supported only on the three fixed cells of `Y` cannot
satisfy the displayed equation. The artifact proves this obstruction
and parametrizes all possible commuting involutions by an involution
on the fixed region, an involution on the quotient of the moved
region, and an invariant locally constant bit function.

Every completion also satisfies `P_1(Z)^2!=1`. Indeed the required
map `X_0 B_0` is not conjugate to its inverse in `V`, whereas
`Q_1(Z)` is reversed by `Y`. If `P_1(Z)^2=1`, the compiler equation
would make `X_0 B_0=P_1 Q_1 P_1` conjugate to `Q_1`, a contradiction.
The nonreversibility proof uses the signed prefix-length changes at
the four nontrivial fixed germs and their eventual-tail classes.

The native word `p_1` has unreduced length `36` and image
`x_23(t_1)`, so its square is a true native kernel word of unreduced
length `72`. Adding that row excludes this prescribed diagonal
architecture. Twisting one component by tail complementation makes
the required map reversible, but not a square in `V`, and is therefore
excluded as well: with `P_1^2=1`, the required map would be conjugate
to the square `Q_1=(C^-1 Z C Y)^2`.

More generally, for disjoint finite-prefix diagonal components of these
two specified orientations, let their counts be `n_+` and `n_-`.
A completion preserving `P_1^2=1` necessarily has `n_+=n_-` with
both counts even. Thus all two-component orientation choices fail;
four components, two in each orientation, are the first counts not
excluded by these tests, not a constructed completion.

The square is not an explicitly imposed row of `T_8` and was not
assumed in the completion criterion; no non-derivability claim is made.
The exclusions concern these specified diagonal components, not
arbitrary embeddings of `V` or all maps from `Q`.

No completing `Z` is constructed. A completion would give a comparison
with Thompson's `V`; disproving a uniform matrix gap this way would
also require hyperlinearity of `V`, which is not assumed or established.
The exact replay script checks the constants and the Thompson rows,
not the existence of a completion. The proof is written, not newly
Lean-verified.

DERIVATION
seven-cell-core-reduces-thompson-completion-to-one-equation
