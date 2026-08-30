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
`304 sqrt(gamma)+2 gamma`.  At a fixed positive distance this is an error
floor, whereas the central-embedding characterization of Z-stability
requires errors tending to zero.

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
fixed centrality error after transporting Z-copies, or another absorption
criterion stable under the available complete-distance control.  Neither
step is presently established.
