---
rg: 2
id: thompson-f-two-transitive-irrational-orbit-colorings-proof
kind: route
title: Irrational points have trivial germ groups, so agreement at an irrational point is equality of H-orbit labels, and Baire category turns the interior dichotomy into transitivity on irrational orbits
target: thompson-f-two-transitive-irrational-orbit-colorings
requires:
  - thompson-f-two-transitive-disagreement-sets-are-self-similar
  - thompson-f-two-transitive-stabilizers-minimal-not-confined
---

Notation as in the target. Imported statements, verbatim:

- From `thompson-f-two-transitive-disagreement-sets-are-self-similar`:
  (SS1) "`D(ω,ω')` is closed, `D(ω,ω') = D(ω',ω)`, `D(gω,gω') = g D(ω,ω')` for
  `g ∈ F`, and `D(ω,ω') = ∅` iff `ω = ω'`";
  (SS2) "All disagreement sets of distinct pairs form one `F`-orbit of closed
  sets. Call a representative `D_0`. It is a compact subset of `(0,1)`";
  (SS6) "`D_0` has infinitely many connected components and no isolated
  points, i.e. it is a perfect set".
- From `thompson-f-two-transitive-stabilizers-minimal-not-confined`, item 2:
  (MIN) "`H` acts minimally on `(0,1)`: every `H`-orbit is dense".

Recall `D(ω_1,ω_2) = { x : ω_2 ∉ G_x ω_1 }`, so `x ∉ D(ω_1,ω_2)` iff
`ω_2 ∈ G_x ω_1`.

**Step 1 (item 1: `F_y = G_y` at irrational `y`).** An element that is the
identity near `y` fixes `y`, so `G_y ⊆ F_y`. Conversely let `g ∈ F` fix an
irrational `y`. The breakpoints of `g` are dyadic, so `y` is not one of them,
and on a neighbourhood of `y` we have `g(x) = 2^k x + b` with `k ∈ Z` and `b`
a dyadic rational. From `g(y) = y` we get `(2^k - 1) y = -b`. If `k ≠ 0`, then
`y = b/(1 - 2^k)` is rational, which is false. So `k = 0`, then `b = 0`, and
`g` is the identity near `y`. Hence `F_y = G_y`.

For the bijection, first well-definedness and injectivity together. Let
`a, a' ∈ F`. We claim `a'H ∈ G_y·aH` iff `H a'^{-1} y = H a^{-1} y`.

- If `a'H = k a H` with `k ∈ G_y = F_y`, then `a' = k a h` with `h ∈ H`, so
  `a'^{-1} y = h^{-1} a^{-1} k^{-1} y = h^{-1} a^{-1} y ∈ H a^{-1} y`.
- If `a'^{-1} y = h a^{-1} y` with `h ∈ H`, put `k = a' h a^{-1}`. Then
  `k^{-1} y = a h^{-1} a'^{-1} y = a h^{-1} h a^{-1} y = y`, so
  `k ∈ F_y = G_y`, and `k aH = a' h H = a'H`.

The first bullet (with `a'H = aH`, `k = 1`) shows the map does not depend on
the coset representative, and the claim shows it is well defined on
`G_y`-orbits and injective. It is onto: every `H`-orbit in `F·y` is `H z`
with `z = a^{-1} y` for some `a ∈ F`, the image of `G_y·aH`.

**Step 2 (item 2: colorings).** Let `O` be an irrational orbit and `y ∈ O`.
Then `F·y = O`, and the claim in Step 1 with `ω_1 = aH`, `ω_2 = a'H` reads:
`c_{ω_1}(y) = c_{ω_2}(y)` iff `ω_2 ∈ G_y ω_1` iff `y ∉ D(ω_1,ω_2)`. Its first
bullet shows `c_{ω_1}` does not depend on the choice of `a`. For `g ∈ F`,
`gω_1 = (ga)H`, so `c_{gω_1}(y) = H a^{-1} g^{-1} y = c_{ω_1}(g^{-1} y)`.

**Step 3 (item 3: bad orbits).** Let `y ∈ (0,1)`. The point `y` is bad iff
there are `ω_1, ω_2` with `ω_2 ∉ G_y ω_1`, i.e. with `y ∈ D(ω_1,ω_2)`. Such a
pair is distinct, because `D(ω_1,ω_1) = ∅` (SS1). By (SS2), the disagreement
sets of distinct pairs are exactly the sets `g D_0`, `g ∈ F`. So `y` is bad
iff `y ∈ g D_0` for some `g`, iff `g^{-1} y ∈ D_0` for some `g`, iff `F·y`
meets `D_0`. The last condition depends only on the orbit, so for an orbit
`O ⊂ (0,1)`: some point of `O` is bad iff every point is iff `O` meets `D_0`.
If `z ∈ O ∩ D_0`, then every disagreement set of a distinct pair is some
`g D_0` and contains `gz ∈ O`. Conversely `D_0` is itself such a set.

Counting. `D_0` is nonempty (it is the disagreement set of a distinct pair,
nonempty by SS1), compact and perfect (SS6). A nonempty perfect compact
metric space is uncountable: otherwise it is a countable union of singletons,
each nowhere dense because no point is isolated, contradicting the Baire
category theorem. `F` is countable, since an element is determined by finitely
many dyadic breakpoints and values, so every `F`-orbit is countable. The
rationals are countable. So `D_0` contains uncountably many irrationals, and
these lie in uncountably many orbits, each bad and irrational.

**Step 4 (item 4: partition stabilizer).** Let `O` be a bad irrational orbit.

- Injectivity. If `ω_1 ≠ ω_2`, then by Step 3 `D(ω_1,ω_2)` meets `O`, say at
  `y`, and by Step 2 `c_{ω_1}(y) ≠ c_{ω_2}(y)`.
- The colouring of `ω` itself. With `a = 1`, `c_ω(y) = H y`: each point of `O`
  is coloured by its own part of `P_O`.
- `H` fixes each part. If `g ∈ H` and `P = H z`, then `gP = gHz = Hz = P`.
- Conversely let `g ∈ F` fix every part. Then `g^{-1}` also does, so
  `g^{-1} y ∈ H y` for every `y ∈ O`, and by Step 2
  `c_{gω}(y) = c_ω(g^{-1} y) = H g^{-1} y = H y = c_ω(y)`. By injectivity
  `gω = ω`, i.e. `g ∈ H`.
- At least two parts. Pick `y ∈ O ∩ D_0`. Then `y` is bad (Step 3), so `G_y`
  has at least two orbits on `Ω`, and by Step 1 `H` has at least two orbits
  on `F·y = O`.
- Density. Each part is an `H`-orbit in `(0,1)`, dense by (MIN).

**Step 5 (item 5: dichotomy).** `D_0 ⊂ (0,1)` is compact, and either its
interior is empty or it is not.

*Empty interior.* A compact subset of the line with empty interior contains
no interval, so its components are points. With (SS6), `D_0` is a nonempty
compact, perfect, totally disconnected metric space, i.e. a Cantor set
(Brouwer's characterization). This matches the reading of "Cantor" in
`thompson-f-two-transitive-disagreement-sets-are-not-cantor`: "A compact
perfect subset of the line with empty interior is a Cantor set". Each
`g D_0` is closed with empty interior, since `g` is a homeomorphism of
`[0,1]`, so it is nowhere dense. `F` is countable, so `F·D_0 = ∪_g g D_0` is
meagre in `(0,1)`, and so is `Q ∩ (0,1)`. By Step 3 the good points are
exactly `(0,1) \ F·D_0`. This set is `F`-invariant and comeagre. Removing `Q`
leaves a comeagre set of good irrational points, nonempty by the Baire
category theorem. For each good irrational `y`, `G_y` is transitive on `Ω`,
so by Step 1 `H` has exactly one orbit on `F·y`. This is (A).

*Nonempty interior.* Let `I ⊆ D_0` be a nonempty open interval, and let
`x ∈ (0,1)`. By (MIN) the orbit `Hx` is dense, so some `h ∈ H ⊆ F` has
`hx ∈ I ⊆ D_0`. So `F·x` meets `D_0`, and `x` is bad (Step 3). For irrational
`y`, `G_y` is not transitive, so by Step 1 `H` has at least two orbits on
`F·y`. This is (B).

The two cases are exclusive: in (A) some irrational orbit carries a single
`H`-orbit, and in (B) none does. So for a fixed action, (A) holds iff `H` is
transitive on some irrational orbit, and (B) holds iff it is transitive on
none. `...-are-not-cantor` asserts (B) for every action and
`...-have-no-interior` asserts (A) for every action, which gives the two
equivalences under "What this changes".

**Step 6 (item 6: product splitting).** Let `y` be irrational.

- *Subgroups.* `A_y` is the increasing union over dyadic `c < y` of the groups
  of elements supported in `[0,c]`, so it is a subgroup. The same holds for
  `B_y`. Elements `a ∈ A_y`, `b ∈ B_y` have disjoint supports `[0,c]` and
  `[d,1]` with `c < y < d`, so they commute, and `A_y ∩ B_y = 1`. Both lie in
  `G_y`.
- *`G_y ⊆ A_y B_y`.* Let `k` be the identity on `(y-ε, y+ε)`. Choose dyadic
  `c ∈ (y-ε, y)` and `d ∈ (y, y+ε)`. Let `k^-` be `k` on `[0,c]` and the
  identity on `[c,1]`, and `k^+` be the identity on `[0,d]` and `k` on
  `[d,1]`. Since `k` fixes `c` and `d` and is the identity near them, both are
  in `F`, as in Step 5 of
  `thompson-f-two-transitive-disagreement-sets-self-similar-proof`. Since `k`
  is the identity on `[c,d]`, `k = k^- k^+`, with `k^- ∈ A_y` and
  `k^+ ∈ B_y`. So `G_y = A_y × B_y`, an internal direct product.
- *Actions on the factors.* Put `L = Ω/B_y` and `R = Ω/A_y`. Because `A_y`
  and `B_y` commute, `a B_y ω_1 = B_y a ω_1`, so `A_y` permutes `L`. It fixes
  every point of `R`, since `A_y a ω_1 = A_y ω_1`. Symmetrically for `B_y`.
  The map `Φ(ω_1) = (B_y ω_1, A_y ω_1)` satisfies
  `Φ(ab ω_1) = (a B_y ω_1, b A_y ω_1)`.
- *Injective* (for every irrational `y`). Suppose `Φ(ω_1) = Φ(ω_2)`. Then
  `ω_2 = a ω_1 = b ω_1` with `a` supported in some `[0,c]`, `c < y`, and `b` in
  some `[d,1]`, `d > y`. The element `a` lies in `G_x` for every `x ∈ (c,1]`,
  so `D(ω_1,ω_2) ⊆ [0,c]`. Likewise `b ∈ G_x` for `x ∈ [0,d)`, so
  `D(ω_1,ω_2) ⊆ [d,1]`. Hence `D(ω_1,ω_2) = ∅`, and `ω_1 = ω_2` by (SS1).
- *Surjective* (for good `y`). Given `ω_1, ω_2`, transitivity of
  `G_y = A_y B_y` gives `ω_2 = a b ω_1`. Put `ω_3 = b ω_1`. Then
  `B_y ω_3 = B_y ω_1` and `A_y ω_3 = A_y a^{-1} ω_2 = A_y ω_2`, so
  `Φ(ω_3) = (B_y ω_1, A_y ω_2)`.
- *Stabilizer.* By injectivity, `ab ∈ H` iff `Φ(abω) = Φ(ω)` iff
  `a B_y ω = B_y ω` and `b A_y ω = A_y ω`. Taking `b = 1`, the first condition
  alone says `a ∈ H ∩ A_y`. Taking `a = 1`, the second alone says
  `b ∈ H ∩ B_y`. So `ab ∈ H` iff `a ∈ H` and `b ∈ H`, i.e.
  `H ∩ G_y = (H ∩ A_y) × (H ∩ B_y)`.

This completes the proof of the target.

**Remark (what the reframing does not give).** Neither case of item 5 is
refuted here. In case (A), a proof of `...-are-not-cantor` must show that a
maximal subgroup `H` which is transitive on an irrational orbit `F·y`, i.e.
`F = H F_y` with `F_y = A_y × B_y` germ-free, cannot have exactly two double
cosets. In case (B), a proof of `...-have-no-interior` must show that a
part-wise partition stabilizer of every bad irrational orbit, with at least
two dense parts on every irrational orbit, cannot have exactly two double
cosets.
