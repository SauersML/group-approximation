---
rg: 2
id: toms-conflict-free-face-labellings-never-exist-proof
kind: route
title: A conflict-free missed-face labelling would give a map of the cube to R^N minus 0 whose boundary restriction has degree plus or minus one
target: toms-conflict-free-face-labellings-never-exist
requires: [toms-level-two-spanning-reduces-to-relative-hex, toms-spanning-defect-is-superadditive]
---

Notation is that of the claim.

## Part 1: labelling lemma

Suppose `l` is a conflict-free missed-face labelling. The barycentric subdivision of the cell
complex has one vertex `b(c)` for each cell `c`. Its simplices are the chains
`c_0 < c_1 < ... < c_k`, where `<` means "is a face of". Define `f : I^N -> R^N` by
`f(b(c)) = l(c)`, extended linearly on each simplex.

*`f` misses 0.* Any two cells of a chain are comparable, so conflict-freeness makes the labels
of a chain pairwise non-antipodal. A set of vertices of the cross-polytope with no antipodal
pair lies in `{sigma_i e_i : i in J}` for one sign choice `sigma`. Every convex combination
of such vectors has coordinates of sign `sigma_i` summing in absolute value to `1`, so it is
not `0`.

*Boundary behaviour.* Let `x in dI^N`. The simplex containing `x` in its relative interior is
a chain whose top cell `c_k` is the open cell containing `x`. If `x_nu = 0` then `c_k` lies in
the face `{x_nu = 0}`, and so do all its faces `c_j`. So no `l(c_j)` is `-e_nu`, and
`f(x)_nu >= 0`. Symmetrically, `x_nu = 1` gives `f(x)_nu <= 0`.

*Homotopy.* Put `r(x) = x - (1/2, ..., 1/2)` and `h_t = t f + (1 - t)(-r)` on `dI^N`. Take
`x in dI^N` and a coordinate `nu` with `x_nu in {0, 1}`. Say `x_nu = 0`: then
`-r(x)_nu = 1/2` and `f(x)_nu >= 0`, so `h_t(x)_nu > 0` for `t < 1`. The case `x_nu = 1` is
symmetric. With `h_1 = f != 0` this shows that `h` is a homotopy in `R^N \ {0}` from `-r` to
`f` on `dI^N`.

*Contradiction.* The map `-r|dI^N` has degree `(-1)^N` into `S^(N-1)` after normalising. But
`f|dI^N` extends to `f : I^N -> R^N \ {0}`, so it is null-homotopic and has degree `0`.

## Part 2: partitions and levels

Give each cell of a piece `Omega` the label `n_(F(Omega))`. If a cell `c` of `Omega` lies in
`F(Omega)` then `Omega` meets `F(Omega)`, which is impossible. So this is a missed-face
labelling, and by Part 1 some `c <= c'` have `l(c) = -l(c')`. Since `c` is a single cell,
`l(c)` and `l(c')` come from pieces `Omega ∋ c` and `Omega' ∋ c'`. They are different pieces
because their labels differ. Their closures meet, since `c ⊂ cl(c')`. They picked
`n_(F(Omega)) = -n_(F(Omega'))`, which are the two opposite faces of one coordinate.

Now let the pieces be the level components of a cell-constant usc `delta`. Then
`{delta >= t}` is closed, so `delta(c) >= delta(c')` for `c <= c'`. If `delta(c) = delta(c')`
then `c ∪ c'` is a connected subset of one level set, and `Omega = Omega'`. So
`delta(c) > delta(c')`.

## Part 3: the route is vacuous

Part 2 applies to every finite cell partition in which each piece misses a face. That covers
the following:
- every cell-constant face counterexample, where every piece fails at least one coordinate;
- the slit-wall configuration refuting `R1(2)` (`toms-level-two-spanning-reduces-to-relative-hex`,
  and the SAT control `N = 2, n = 4, cap 2` of `toms-spanning-defect-is-superadditive`);
- the grown normal forms of either.

So "a counterexample to `R1(3)` admits a conflict-free colouring" is false for every
configuration. Its contrapositive therefore proves nothing about `R1(3)`: an argument of that
shape would equally prove `R1(2)`, which is false. Conflicts always exist, and by Part 2 they
occur where a strictly higher level sits in the closure of a lower one. A proof of `R1(3)`
must see how many coordinates a component fails, not only one missed face per component.

## Part 4: soundness of the computations

- *Lex-leader breaking.* The model of `face_form_sat.py` is invariant under the hyperoctahedral
  group acting on cells and labels. For each non-identity `g` the constraint `V <=_lex g(V)`
  holds for the lex-least member of the orbit of any model. `V` is the vector of level bits in
  a fixed cell order, and truncating it keeps this true. So SAT and UNSAT are unchanged.
- *Jack.* Take levels `{0, 1}` on the cells of `W` (cells with some index equal to `n`, `n`
  even) and level 2 on the eight closed octants shrunk off `W`. Suppose each level-1 component
  fails two coordinates and each level-0 component fails one. Pull back along the retraction
  of a thin neighbourhood of `W` onto `W`. On indices this map sends `n +- 1` to `n`; it is
  monotone for the face order, has connected fibres, and fixes the boundary indices `0` and
  `2n`. So level components and the faces they meet are preserved. Each octant blob misses the
  three faces through its far corner and does not meet `W`. The result is a face
  counterexample to `F(3)`. So UNSAT on the jack excludes exactly this normal form at that
  resolution. It says nothing about other blob layouts.
