---
rg: 2
id: homeo-circle-three-arc-mixed-identity-proof
kind: route
title: Disjoint supports commute, a nontrivial commutator forces an overlap, and three overlaps would reverse a cyclic orientation
target: homeo-circle-three-arc-commutator-word-is-mixed-identity
requires: []
artifacts:
  - research/artifacts/solve-mixed-identity-undecidable-2026-09-13.md
---

Elementary and self-contained.

**Step 1 (disjoint supports commute).** Let `f, h` be bijections of a set with
`supp(f) ∩ supp(h) = ∅`. Supports are invariant: `f(supp f) = supp f`.
- If `p in supp(h)`, then `h(p) in supp(h)`, so `f h(p) = h(p)`; and `f(p) = p`,
  so `h f(p) = h(p)`.
- If `p in supp(f)`, symmetrically `f h(p) = f(p) = h f(p)`.
- Otherwise both sides give `p`.

**Step 2 (overlap).** For `g in G`, `supp(g a_j g^-1) = g(supp a_j) ⊆ g(A_j)`.
By Step 1, `s_ij(g) != 1` forces `A_i ∩ g(A_j) != ∅`.

**Step 3 (orientation).** Suppose `s_12(g)`, `s_21(g)` and `s_33(g)` are all
nontrivial. By Step 2:
- `A_2 ∩ g(A_1) != ∅` gives `p_1 in A_1` with `g(p_1) in A_2`;
- `A_1 ∩ g(A_2) != ∅` gives `p_2 in A_2` with `g(p_2) in A_1`;
- `A_3 ∩ g(A_3) != ∅` gives `p_3 in A_3` with `g(p_3) in A_3`.

The arcs are disjoint and met in the cyclic order `A_1, A_2, A_3`. So every
triple with one point in each of `A_1, A_2, A_3`, in that order, is positively
oriented, and every triple in `A_2 x A_1 x A_3` is negatively oriented. Thus
`(p_1, p_2, p_3)` is positive and `(g p_1, g p_2, g p_3)` is negative. An
orientation-preserving homeomorphism preserves the orientation of triples of
distinct points. Contradiction: for each `g`, one of `s_12(g), s_21(g), s_33(g)`
is trivial.

**Step 4 (`w(g) = 1`).** If `s_12(g) = 1` or `s_21(g) = 1`, then
`[s_12(g), s_21(g)] = 1`. If `s_33(g) = 1`, then `w(g) = [·, 1] = 1`.

**Step 5 (`w != 1`).** The six words below are alternating products of
nontrivial syllables, so they are reduced in `G * <x>`:

```text
s_12    = a_1 x a_2 x^-1 a_1^-1 x a_2^-1 x^-1
s_21    = a_2 x a_1 x^-1 a_2^-1 x a_1^-1 x^-1
s_12^-1 = x a_2 x^-1 a_1 x a_2^-1 x^-1 a_1^-1
s_21^-1 = x a_1 x^-1 a_2 x a_1^-1 x^-1 a_2^-1
s_33    = a_3 x a_3 x^-1 a_3^-1 x a_3^-1 x^-1
s_33^-1 = x a_3 x^-1 a_3 x a_3^-1 x^-1 a_3^-1
```

Now `w = s_12 s_21 s_12^-1 s_21^-1 · s_33 · s_21 s_12 s_21^-1 s_12^-1 · s_33^-1`.
Its nine junctions:
- `s_12|s_21`, `s_12^-1|s_21^-1`, `s_33|s_21`, `s_21|s_12`, `s_21^-1|s_12^-1`
  and `s_12^-1|s_33^-1` meet an `x`-syllable against a constant, so nothing
  cancels.
- `s_21|s_12^-1` cancels `x^-1 x` and merges `a_1^-1 a_2`.
- `s_12|s_21^-1` cancels `x^-1 x` and merges `a_2^-1 a_1`.
- `s_21^-1|s_33` merges `a_2^-1 a_3`.

The merged constants are nontrivial, because `a_i != a_j` for `i != j` (disjoint
nonempty supports), and each is flanked by `x`-syllables. So the product is an
alternating word of nontrivial syllables. By the normal form theorem for free
products, `w != 1`.

**Interval version.** Steps 1 and 2 hold verbatim. If `s_12(g)` and `s_21(g)`
were both nontrivial, there would be `p_1 in supp(a_1)` with `g(p_1) in supp(a_2)`
and `p_2 in supp(a_2)` with `g(p_2) in supp(a_1)`. Then `p_1 < p_2` but
`g(p_1) > g(p_2)`, contradicting monotonicity. The first three junctions above
show `[s_12, s_21] != 1`.

**Step 6 (examples in F and T).** Let `a < b` be dyadic. As in Lemma L1 of
`thompson-t-mixed-identity-decision-procedure-proof`, there is a piecewise-linear
homeomorphism `λ : [0,1] -> [a,b]` with dyadic breakpoints and slopes that are
powers of 2. For nontrivial `f in F`, extending `λ f λ^-1` by the identity gives
a nontrivial element of `F` supported in `(a, b)`. Placed on an arc with dyadic
endpoints, it gives one of `T`. Three disjoint dyadic arcs then give (CA1) in `T`,
and two disjoint dyadic intervals give the interval version in `F`. `∎`
