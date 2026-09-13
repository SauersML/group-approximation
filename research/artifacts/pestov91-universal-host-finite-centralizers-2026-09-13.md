# Universal Kazhdan hosts inside finite centralizers

2026-09-13. Written proof, not Lean-verified. This strengthens the
[universal locally finite host](pestov91-universal-locally-finite-host-2026-09-13.md)
by controlling the position of new subgroups relative to a prescribed
finite subgroup. The only group-theoretic existence inputs are the
repository's minimal-subshift theorem and its compatible matrix-tower
embedding theorem. The corner and centralizer arguments are proved here.

## Theorem

Choose the fixed eighteen-involution infinite simple Kazhdan LEF host
`S=EL_3(R)`, where `R=LC(X,F_2) semidirect Z` and the infinite minimal
binary subshift `(X,T)` factors onto the universal odometer. Let

`D = union_j SL_(3j!)(F_2) <= S`

be its diagonal locally finite core, with the matrix-tower embeddings
specified in the preceding proof. For every finite subgroup `F <= D`
and every integer `r >= 1`, there is an infinite simple Kazhdan LEF group
`H=H(F,r)` such that:

1. Every countable locally finite group embeds in `H`.
2. There is an injective homomorphism
   `F x (H^r semidirect Sym(r)) -> S` whose restriction to `F` is its
   prescribed inclusion. The symmetric group permutes the `r` factors.

In particular `C_S(F)` contains `r` mutually commuting isomorphic
infinite simple Kazhdan universal hosts, together with elements realizing
every permutation of those factors. For `r=1`, **every countable locally
finite group embeds in a simple Kazhdan LEF subgroup of `C_S(F)`**.

The quantifier on `F` is `F <= D`, not an arbitrary finite subgroup of
`S`. Neither `H` nor its embedding is asserted to be independent of
`F,r`, and no isomorphism `H ~= S` is needed or claimed.

## 1. Cyclic corners retain the whole construction

Write `pi_m:X -> Z/mZ` for the compatible cyclic factors. Fix `m >= 1`,
put `C=pi_m^{-1}(0)` and `q=1_C`. The first return time to `C` is exactly
`m`. The system `(C,T^m)` is infinite and minimal. The `m` translates of
`C` partition the infinite space `X`, so `C` is infinite. Every visit of
a point of `C` to `C` occurs at a multiple of `m`; density of its full
`T`-orbit therefore gives density of its `T^m`-orbit in `C`.

It is also a finite-alphabet subshift: code `x in C` by the consecutive
length-`m` blocks `x_[km,(k+1)m)` for `k in Z`. This is a continuous
injective map into `(alphabet^m)^Z`, intertwines `T^m` with the shift,
and has closed image. Concatenation is its inverse on that image.

It still factors onto the universal odometer. For every positive `n`,
the value `pi_(mn)(x)` of a point of `C` is a multiple of `m` modulo `mn`.
Thus

`eta_n(x) = pi_(mn)(x)/m mod n`

is well-defined, continuous, onto and compatible under divisibility.
It satisfies `eta_n(T^m x)=eta_n(x)+1`. These maps give an onto map to
`lim_j Z/j!Z`: surjectivity follows from compactness and the nested
nonempty fibers of compatible finite coordinates.

Let `u f u^{-1}=f circ T^{-1}` in `R`. Since `q` is invariant under
`T^m`, `v=q u^m` is invertible in the unital corner `A=qRq`, with identity
`q` and inverse `q u^{-m}`. A homogeneous term `q f u^k q` vanishes unless
`m` divides `k`, because `C` and `T^k C` are otherwise disjoint. Hence

`A = qRq ~= LC(C,F_2) semidirect_(T^m) Z`.                 (1)

The displayed map is injective by uniqueness of homogeneous coefficients
and surjective by the preceding observation. The minimal-subshift theorem
now makes `EL_3(A)` infinite, Kazhdan, LEF, and simple: the possible scalar
centre is trivial over `F_2`. The inherited odometer factor and compatible
regular representations make it universal for countable locally finite
groups. This argument does not require the induced alphabet to be binary.

## 2. Flattening over a full cyclic corner

For `0 <= a,b < m`, let

`E_ab = 1_(pi_m^{-1}(a)) u^(a-b)`.

These are full matrix units with `E_00=q` and sum of the diagonal units
equal to `1`. They give mutually inverse unital ring isomorphisms

`M_m(A) -> R,  (a_ab) -> sum_(a,b) E_a0 a_ab E_0b`,

`R -> M_m(A),  x -> (E_0a x E_b0)_(a,b)`.                (2)

After applying `M_3`, this identifies `M_3(R)` with `M_(3m)(A)` and,
at the level of elementary groups,

`EL_3(R) = EL_(3m)(A)` under that identification.          (3)

Here is the elementary verification, valid for noncommutative `A`.
An outer root `e_ij(x)`, `i != j`, becomes a product of flattened roots
whose coefficients are the entries of `x` in (2). Those roots commute,
since their row colour is `i` and column colour is `j`. Conversely a
flattened root between different colours is such an outer root. For
distinct coordinates `s,t` in the same colour, choose a coordinate `w`
in another colour. For every `a in A`,

`[I+a e_sw, I+q e_wt] = I+a e_st`.                       (4)

This proves the reverse inclusion in (3). In particular all constant
invertible `3m`-by-`3m` matrices over `F_2` belong to this group: their
determinant is one and Gaussian elimination expresses them as elementary
matrices.

## 3. Put a free multiplicity space beside the prescribed subgroup

Choose `N=j!` with `F <= SL_(3N)(F_2)` in the specified tower core.
Set `m=3rN`, and use the corner `A=1_(pi_m^{-1}(0)) R
1_(pi_m^{-1}(0))`. The cyclic factors exist for this `m`, whether or not
`m` itself is a factorial.

Refinement of matrix units is the exact identity

`E_ab^(N) = sum_(t=0)^(3r-1) E_(a+tN,b+tN)^(m)`.        (5)

Consequently, in (2)--(3), and after the fixed reordering of coordinates
`(colour,a,t)` as `((colour,a),t)`, every element `f in F` is represented
by

`f tensor I_(3r)` in `M_(3N)(F_2) tensor M_(3r)(A)`.      (6)

The notation in (6) is legitimate even though `A` need not commute:
the first tensor factor has scalar entries in the central field `F_2`.
It follows directly by multiplication that `I_(3N) tensor B` commutes
with `F` for every `B in GL_(3r)(A)`.

Set `H=EL_3(A)`, the universal host from section 1. Embed `H^r` into
`EL_(3r)(A)` by block diagonal matrices. Permutations of the `r` blocks
are constant matrices over `F_2`, hence elementary. They normalize this
copy of `H^r` and permute its factors in the required manner. The block
monomial map

`H^r semidirect Sym(r) -> EL_(3r)(A)`                    (7)

is injective: the nonzero block positions recover the permutation, and
then the blocks recover the elements of `H`. Its further amplification
`B -> I_(3N) tensor B` lies in `EL_(3m)(A)`, because the amplification of
each elementary root is a product of elementary roots. By (3) this gives
an injective copy `W <= C_S(F)` of the group in (7).

Finally `Z(W)=1`. An element centralizing each of the nontrivial factors
`H` cannot permute them; its remaining components lie in `Z(H)=1`.
Since `W` centralizes `F`, an element of `F intersect W` belongs to
`Z(W)`. Thus `F intersect W=1`, and multiplication gives the claimed
embedding `F x W -> S`, fixing `F` pointwise. This finishes the proof.

## 4. What the strengthening supplies

The original universality statement supplies an embedding of each
locally finite input somewhere in `S`. Here the finite subgroup `F` is
already in place and is kept fixed. One can put a whole infinite simple
Kazhdan universal host beside it, or any finite number of isomorphic
commuting hosts together with their permutation symmetries.

Thus the prescribed finite subgroup is a direct factor of a finitely
generated Kazhdan LEF subgroup with infinite simple universal factors.
Finite products and finite extensions preserve property (T), and LEF
passes to subgroups of `S`. All these subgroups are therefore also sofic,
hyperlinear, and operator MF. The centralizer conclusion is an algebraic
statement inside `S`, not a statement about centralizers in a sofic
ultraproduct.

All three new graph claims have full written arguments above. No new
literature theorem is imported: section 1 proves the return-system
facts directly, and the base host proof already records its Gao--Li
odometer realization and Ershov--Jaikin-Zapirain property-(T) inputs.
No global priority claim is made.

## 5. Validation

The [MSI receipt](pestov91-finite-centralizers-cairn-receipt-2026-09-13.json)
records successful Cairn 2.13.1 check and preview on the archived research
snapshot at `3bf9156f5c1f673c45ce7b739f9f816dcfcf7be9`, overlaid with
these six new graph nodes and their written proof. It parsed 10,176
claims and 10,437 routes, with zero baseline or final graph errors; the
three new claims all resolved as established. The run took 30.279 seconds
on MSI using one Python 3.12 process.

As in the preceding host validation, the archive-backed runner replaced
source and HEAD loading while retaining Cairn's parser, lint, solver,
check and preview policies. Artifact existence used the exact tracked
path manifest plus the delta; revision-pinned artifacts used the warm
repository's Git object database. The receipt and this validation
paragraph were added after that run. This verifies the research-graph
wiring, not the mathematical arguments by Lean.
