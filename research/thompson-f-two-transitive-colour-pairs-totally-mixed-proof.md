---
rg: 2
id: thompson-f-two-transitive-colour-pairs-totally-mixed-proof
kind: route
title: Every colour pair occurs along every pair, point components are totally mixed, and the Cantor case is a subset-stabilizer model
target: thompson-f-two-transitive-colour-pairs-are-totally-mixed
requires:
  - thompson-f-two-transitive-disagreement-sets-are-self-similar
  - thompson-f-two-transitive-irrational-orbit-colorings
  - thompson-f-two-transitive-stabilizers-minimal-not-confined
---

Notation as in the target. "S1.k" is item k of
`thompson-f-two-transitive-disagreement-sets-are-self-similar`, and "S2.k" is
item k of `thompson-f-two-transitive-irrational-orbit-colorings`. Throughout,
`O` is a bad irrational orbit, which exists by S2.3. Its colours are the
parts of `P_O`, and there are at least two of them by S2.4.

**Preliminary.** For `ω_1, ω_2 ∈ Ω`, the set
`{ y ∈ O : c_{ω_1}(y) ≠ c_{ω_2}(y) }` lies in `D(ω_1,ω_2)` by S2.2. That set
is closed by S1.1, so `D^{ij}(ω_1,ω_2) ⊂ D(ω_1,ω_2)`. By S2.2,
`c_{gω_1}(gy) = c_{ω_1}(y)`, and `O` is `F`-invariant. Hence

(E) `D^{ij}(gω_1,gω_2) = g D^{ij}(ω_1,ω_2)` for all `g ∈ F`.

**Item 1.** Let `i ≠ j` be colours, and pick `y ∈ i` and `y' ∈ j`. Since `O`
is one `F`-orbit, there is `f ∈ F` with `f(y') = y`. With `ω = H` (so `a = 1`
in S2.2):
- `c_ω(y) = H·y = i`;
- `c_{fω}(y) = c_ω(f^{-1}y) = c_ω(y') = H·y' = j`.

So `y` lies in the set whose closure is `D^{ij}(ω,fω)`, and
`D^{ij}(ω,fω) ≠ ∅`. In particular `y ∈ D(ω,fω)`, so `fω ≠ ω` by S1.1.
Given any ordered pair `ω_1 ≠ ω_2`, 2-transitivity gives `g ∈ F` with
`gω = ω_1` and `gfω = ω_2`. By (E),
`D^{ij}(ω_1,ω_2) = g D^{ij}(ω,fω) ≠ ∅`.

**Item 2.** Let `D = D(ω_1,ω_2)`, let `p ∈ D` have component `{p}` in `D`,
and let `i ≠ j`. Suppose `p ∉ D^{ij}(ω_1,ω_2)`. Choose an open interval
`V ∋ p` with `V ∩ D^{ij}(ω_1,ω_2) = ∅`.
- There are `a < p < b` in `V` with `a, b ∉ D`. Otherwise `D` would contain
  `[p,p+ε)` or `(p−ε,p]` for some `ε > 0` (`D` is closed and `p ∈ (0,1)` by
  S1.2), and the component of `p` would not be `{p}`.
- Since `b ∉ D`, S1.3 applied to the pair `(ω_1,ω_2)` at `b` gives `α` with
  `D(ω_1,α) = D ∩ [0,b)` and `D(α,ω_2) = D ∩ (b,1]`.
- Since `a ∉ D ⊃ D(α,ω_1)`, S1.3 applied to the pair `(α,ω_1)` at `a` gives
  `β` with `D(α,β) = D(α,ω_1) ∩ [0,a) = D ∩ [0,a)` and
  `D(β,ω_1) = D(α,ω_1) ∩ (a,1] = D ∩ (a,b)`. (S1.1 gives `D(α,ω_1) =
  D(ω_1,α)`.)
- `p ∈ D ∩ (a,b) = D(β,ω_1)`, so `β ≠ ω_1` by S1.1.

Now use S2.2 on `O`.
- If `c_{ω_1}(y) ≠ c_β(y)`, then `y ∈ D(β,ω_1) ⊂ (a,b)`.
- For `y ∈ O ∩ (a,b)`: `y ∉ D ∩ [0,a) = D(α,β)`, so `c_β(y) = c_α(y)`; and
  `y ∉ D ∩ (b,1] = D(α,ω_2)`, so `c_α(y) = c_{ω_2}(y)`.

Hence
`{ y ∈ O : c_{ω_1}(y) = i, c_β(y) = j } ⊂ (a,b) ∩ { y ∈ O : c_{ω_1}(y) = i,
c_{ω_2}(y) = j } ⊂ V ∩ D^{ij}(ω_1,ω_2) = ∅`.
So `D^{ij}(ω_1,β) = ∅` with `ω_1 ≠ β`, contradicting item 1.

**Item 3.** By S1.2, every `D(ω_1,ω_2)` with `ω_1 ≠ ω_2` is a homeomorphic
image `gD_0`, so it has empty interior. A component of a subset of `[0,1]`
with more than one point is an interval with nonempty interior. So every
component of `D(ω_1,ω_2)` is a point, and item 2 gives
`D(ω_1,ω_2) ⊂ D^{ij}(ω_1,ω_2)`. The reverse inclusion is the preliminary.

**Item 4.** Let `Q` be a union of colours with `∅ ≠ Q ≠ O`, and put
`K = { g ∈ F : gQ = Q }`, a subgroup of `F`.
- Each colour is an `H`-orbit, so `H` preserves each colour, and `H ⊂ K`.
- Pick `q ∈ Q` and `r ∈ O ∖ Q`. Since `O` is one `F`-orbit, some `f ∈ F`
  has `fq = r`. Then `fQ ≠ Q`, so `K ≠ F`.

By item 1 of `thompson-f-two-transitive-stabilizers-minimal-not-confined`,
`H` is a maximal subgroup of `F`. So `K = H`. This uses only that `O` is a
bad irrational orbit, so it holds in both cases of S2.5.

**Item 5.** Assume `D_0` has empty interior, and let `P` be a colour. Put
`S_{ω_1} = { y ∈ O : c_{ω_1}(y) = P }`.
- For `ω_1 = aH`, S2.2 gives `c_{ω_1}(y) = H·a^{-1}y`. So `y ∈ S_{ω_1}` iff
  `a^{-1}y ∈ P`, that is, `S_{aH} = aP`. In particular `aP` depends only on
  `aH`.
- If `aP = bP`, then `b^{-1}a ∈ Stab_F(P) = H` by item 4 with `Q = P`
  (`P ≠ O`, since there are at least two colours). So `aH = bH`, and
  `aH ↦ aP` is injective. It is onto `F·P` and commutes with `F` by its
  formula.

Now let `aP ≠ bP`, so `ω_1 = aH` and `ω_2 = bH` are distinct. Put
`D = D(ω_1,ω_2)`, and fix a colour `j ≠ P`.
- On `O`, `aP ∖ bP = { c_{ω_1} = P, c_{ω_2} ≠ P }` and
  `bP ∖ aP = { c_{ω_2} = P, c_{ω_1} ≠ P }`. At these points the colourings
  differ, so `cl(aP Δ bP) ⊂ D` by the preliminary.
- `{ c_{ω_1} = P, c_{ω_2} = j } ⊂ aP ∖ bP`. By item 3,
  `D = D^{Pj}(ω_1,ω_2) ⊂ cl(aP ∖ bP)`.
- `{ c_{ω_1} = j, c_{ω_2} = P } ⊂ bP ∖ aP`. By item 3,
  `D = D^{jP}(ω_1,ω_2) ⊂ cl(bP ∖ aP)`.

So `D ⊂ cl(aP ∖ bP) ⊂ cl(aP Δ bP) ⊂ D`, and the same holds with `bP ∖ aP`.
All four sets are equal.

**Reduction to (†).** Suppose `D_0` is a Cantor set, and take `O` and a
colour `P` as above.
- `P` is dense in `(0,1)` by S2.4. Another colour lies in `O ∖ P` and is
  dense as well. So `P` is dense and codense in `O`.
- `Stab_F(P) = H` by item 4. Under the bijection of item 5, the action of
  `H` on `F·P ∖ {P}` is the action of `H = F_ω` on `Ω ∖ {ω}`, which is
  transitive. Also `|F·P| = |Ω| ≥ 3`.
- For `fP ≠ P`, item 5 gives `cl(fP ∖ P) = cl(P ∖ fP) = D(fH,H)`. This is a
  translate of `D_0`, so it is nowhere dense.

So a Cantor-type action gives `O` and `P` as excluded by (†). ∎
