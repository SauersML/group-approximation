# STW Problem XCIX: quantitative and literature audit (2026-08-30)

## Question and status

Problem XCIX asks for a universal positive Kadison--Kastler radius around
every separable Z-stable concrete C*-algebra inside which all nearby
C*-algebras remain Z-stable.  Searches through 2026-08-30 found no later
paper claiming a general solution.  The core sources themselves explicitly
distinguish the known closedness result from the unknown openness result.

## Source-checked positive statements

1. Christensen, Sinclair, Smith, White, and Winter,
   [Perturbations of nuclear C*-algebras](https://arxiv.org/abs/0910.4953),
   Theorem 4.3: if `d(A,B)<gamma<1/420000` and `A` is separable and nuclear,
   then `A` and `B` are *-isomorphic.  Hence the XCIX conclusion holds for
   nuclear `A` at radius `1/420000`.  The theorem is on an arbitrary Hilbert
   space; separability of the Hilbert space is only needed for the stronger
   unitary-conjugacy theorem later in that paper.

   Since Kadison--Kastler distance is symmetric, Theorem 4.3 can instead be
   applied to the ordered pair `(B,A)`.  Therefore the same radius proves the
   XCIX conclusion whenever `B` is separable and nuclear, even if the given
   Z-stable algebra `A` is not nuclear.  Separability of `B` is needed for
   this reversed application; nuclearity of `B` alone is not enough to invoke
   the quoted theorem.

2. The same paper, Corollary 4.6: for separable strongly self-absorbing `D`,
   D-stable separable unital subalgebras containing a fixed ambient unit form
   a closed subset in Kadison--Kastler distance.  Corollary 4.7 transports a
   finite-set embedding of `D` across `A subset_gamma B` when
   `gamma<1/12600000`, with error `152 sqrt(gamma)`.

   Closedness here is pointwise in one fixed ambient unital algebra: it says
   that a fixed limit `B` of D-stable `A_n` is D-stable.  It does not exclude
   varying pairs `(A_n,B_n)` with `d(A_n,B_n)->0` and each `B_n` non-D-stable,
   so it does not imply a universal positive radius.

3. Perera, Toms, White, and Winter,
   [The Cuntz semigroup and stability of close C*-algebras](https://arxiv.org/abs/1210.4533),
   Corollary 4.9 gives property `D_(5/2)` for every Z-stable algebra.
   Proposition 4.13 converts ordinary distance to complete distance, and
   Theorem 3.10 gives scaled-Cu isomorphism below complete distance `1/42`.
   Corollary 4.15 states the resulting ordinary radius `1/6422957`.

4. Toms and Winter,
   [Strongly self-absorbing C*-algebras](https://arxiv.org/abs/math/0502211),
   supplies the central-embedding characterization of tensorial absorption
   used in the ultraproduct argument below.  Farah and Szabo,
   [Coronas and strongly self-absorbing C*-algebras](https://arxiv.org/abs/2411.02274),
   distinguishes separable D-stability and D-saturation from tensorial
   absorption for nonseparable algebras; in particular, one must not call a
   nontrivial ultraproduct tensorially Z-stable.

## Exact audit of 1/6422957

Substitution of `k=5/2` into Proposition 4.13 gives

```text
beta = 1585056 gamma,
eta  = 3203122 gamma + 52306848000 gamma^2,
s := 2 eta + 5 gamma
   = 6406249 gamma + 104613696000 gamma^2,
d_cb(A,B) <= 10 gamma/(1-s).
```

For `N=6422957`, the two exact integer margins are

```text
N^2 - 6406249 N - 104613696000 = 2701069556,
N^2 - 6406669 N - 104613696000 =    3427616.
```

The first proves `s<1`; the second proves
`10 gamma/(1-s)<1/42` for `gamma<1/N`.  The remaining hypothesis follows
from `sqrt(2)<3/2` and `1344*2200=2956800<N`.  This confirms the published
radius directly.  The proof's displayed observation
`2 eta+2k gamma < 10^11 gamma < 1` for `gamma<10^-11` is only a coarse
sufficient estimate and should not be mistaken for the final radius.

## Why the known bridges stop

Scaled-Cu agreement is strictly an invariant conclusion; no theorem in the
non-nuclear setting upgrades it to Z-absorption.  Similarly, transporting a
finite-set embedding has commutator error at most the old error plus
`304 sqrt(gamma)+2 gamma`.  This is an additive loss in the available upper
bound, not a lower bound on the centrality of the transported copy.

The raw estimate does not self-improve under iteration.  For paired finite
sets of contractions in `A` and `B` at distance less than `gamma`, let `e_j`
be the centrality error of an embedding after `j` alternating transports.
Writing `Delta=304 sqrt(gamma)+2 gamma`, the commutator triangle inequality
gives

```text
e_(j+1) < e_j + Delta,
e_n     < e_0 + n Delta.
```

Thus the affine update has coefficient one rather than a contraction factor.
The constants `2` used for perturbing either commutator entry cannot be
improved from norm data alone: with `x=diag(1,-1)` and `r=delta e_12` in
`M_2`, `||r||=delta` and `||[r,x]||=2 delta`; the same example with the two
entries interchanged proves sharpness in the second variable.  This only
rules out repeated use of Corollary 4.7 followed by norm triangle
inequalities.  It does not rule out a new argument exploiting relations
among the transported copies or the strongly self-absorbing structure of Z.

The January 2026 preprint
[On stability of distance under some tensor products and some calculations](https://arxiv.org/abs/2601.05154)
concerns Banach-space injective and projective tensor norms.  It does not
give stability of Kadison--Kastler distance under the minimal C*-tensor
product and therefore does not supply a Z-absorption or Morita bridge here.

## Honest frontier

A counterexample below `1/6422957` would have to be a non-Z-stable algebra
with scaled Cu isomorphic to that of a Z-stable algebra, realized in a
concrete representation at that tiny distance.  No such perturbation is
known.  Conversely, a positive solution needs a mechanism that removes the
fixed additive centrality loss after transporting Z-copies, or another absorption
criterion stable under the available complete-distance control.  Neither
step is presently established.

## New vanishing-distance normal form

Let `d(A_n,B_n)->_omega 0`.  Matching each bounded coordinate sequence by a
sequence on the other side with ultranorm-null error proves that the two norm
ultraproducts coincide literally inside the ambient ultraproduct.  If every
`A_n` is unital and Z-stable, increasingly central exact copies of Z in
`A_n` can be transported on increasingly large finite windows to `B_n`.
The transported coordinate maps may be nonunital, but their support
projections converge to the unit of the common ultraproduct.  Their
ultraproduct is therefore a unital copy of Z in the relative commutant of any
prescribed separable subset, so the common ultraproduct is Z-saturated.

This exact relative-commutant property can be iterated without importing any
nonseparable absorption theorem.  Starting from a separable `S_0`, choose a
copy of `Z` commuting with `S_n` and let `S_(n+1)` be generated by the two.
The closure `T` of the increasing union is separable, contains the original
packet, and the chosen copies form a unital embedding
`Z -> T_infinity intersect T'`.  The separable central-sequence criterion
therefore makes `T` tensorially Z-stable.  Thus every separable piece of the
common ultraproduct has a Z-stable hull even though the full ultraproduct
must not be called tensorially Z-stable.

At the coordinate level, for every fixed numbers `m,k`, the worst `m`-point,
`k`-element centrality defect of `B_n` is at most
`304 sqrt(d(A_n,B_n))+2d(A_n,B_n)`.  Hence all fixed windows vanish along a
hypothetical counterexample sequence.  Non-Z-stability can survive only by
moving its obstruction to larger finite windows or smaller tolerances.  This
is an unconditional exact normal form for the asymptotic obstruction, but it
does not reflect Z-stability back to any one coordinate and therefore does
not settle XCIX.

Taking the supremum over all window sizes gives a stronger scalar summary.
With the empty-embedding infimum normalized to `2`, define
`kappa_Z(E)=sup_(m,k) Delta_(m,k)(E)`.  Diagonalization proves that, for
separable unital `E`, this number vanishes exactly when `E` is Z-stable.
Transporting an arbitrary window and then taking the supremum gives

```text
|kappa_Z(A)-kappa_Z(B)|
 <= 304 sqrt(gamma)+2 gamma
```

whenever the close common-unit algebras lie in the quantitative range and
one of them contains a unital copy of `Z` (transport supplies a copy on the
other side).  Thus a counterexample sequence has positive global defects
tending to zero.  This is a Holder-continuous obstruction scalar, but its
zero set need not be open without a new positive-gap theorem.
