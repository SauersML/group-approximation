---
rg: 2
id: bvc-amalgams-have-two-transitive-vertex-actions-proof
kind: route
title: "Count conjugacy classes of cyclically reduced words through double coset necklaces"
target: bvc-amalgams-have-two-transitive-vertex-actions
requires: []
---

Inputs are the normal form theorem and the conjugacy theorem for amalgamated
free products (Lyndon--Schupp, *Combinatorial Group Theory*, Ch. IV §2; the
conjugacy theorem is IV.2.8, cited that way by von Puttkamer--Wu).

**Step 1 (necklace invariant).**  Write `D_A = C\A/C - {C}` and
`D_B = C\B/C - {C}`; both are nonempty.  Take a cyclically reduced
`g = a_1 b_1 ... a_m b_m` with `a_i` in `A - C` and `b_i` in `B - C`.  Two
normal forms of one element differ by `a_i -> c a_i c'`, `b_i -> c' b_i c''`
with `c`'s in `C`, which keeps every double coset.  By IV.2.8 a cyclically
reduced conjugate of `g` is a cyclic permutation followed by conjugation by
`c` in `C`; this rotates the sequence and changes the end letters inside
their double cosets.  So the necklace `(C a_1 C, C b_1 C, ..., C a_m C,
C b_m C)`, up to rotation by pairs, is a conjugacy invariant.  Every necklace
occurs, by choosing representatives.  With `N = |D_A| |D_B|` there are at
least `N^m / m` necklaces of length `m`, hence at least `N^m / m` conjugacy
classes of cyclically reduced elements of length `2m`.

**Step 2 (the length function).**  Every element is conjugate to a cyclically
reduced one.  For elements with a cyclically reduced conjugate of length at
least 2, IV.2.8 makes that length `lambda(g)` well defined and conjugation
invariant.  If `g` is cyclically reduced of length `2m >= 2`, then `g^k` is the
concatenated word, again cyclically reduced, so `lambda(g^k) = |k| lambda(g)`.
Elements conjugate into `A` or `B` have `lambda <= 1` (take `lambda = 0`).

**Step 3 (a virtually cyclic subgroup contributes boundedly).**  Let `V` be an
infinite virtually cyclic subgroup containing an element with `lambda >= 2`.
Pick `z` in `V` generating a finite-index infinite cyclic subgroup, and
replace `<z>` by its normal core, which is still infinite cyclic of finite
index `R`.  Some power `v^R` of an element with `lambda(v) >= 2` lies in `<z>`,
so `lambda(z) >= 2`.  Let `v` in `V` have `lambda(v) = l >= 2`.  Then `v^R = z^s`
with `|s| lambda(z) = R l`, so `v^R` takes at most two values.  In a coset
`<z> f` of `<z>`, conjugation by `f` sends `z` to `z^{e}` with `e = +1` or `-1`:

- if `e = +1`, `(z^j f)^R = z^{jR} f^R` with `f^R` in `<z>`, which is injective in
  `j`, giving at most 2 elements;
- if `e = -1`, conjugating `z^j f` by `z` gives `z^{j+2} f`, so the coset holds at
  most 2 conjugacy classes of `V`.

So the elements of `V` with `lambda = l` fall into at most `2R` classes of `V`,
a bound independent of `l`.

**Step 4 (conclude).**  Let `V_1, ..., V_n` witness BVC.  Each cyclically
reduced `g` of length `2m >= 2` has infinite order and `<g>` is virtually cyclic,
so a conjugate of `g` lies in some `V_i`, with `lambda = 2m`.  By Step 3 the
number of conjugacy classes of `G` with `lambda = 2m` is at most
`B = sum_i 2 R_i`, independent of `m`.  Step 1 gives `N^m / m <= B` for all `m`,
so `N = 1`: `|D_A| = |D_B| = 1`, which is the claim.  The stabilizer `C` of the
base point of `A/C` acts transitively on the other points exactly when
`|C\A/C| = 2`, which is 2-transitivity.  `∎`

Corollary: finite `C` acting transitively on `A/C - {C}` makes `A/C` finite,
so `A` is finite; the same holds for `B`.  So `G` is virtually free.
