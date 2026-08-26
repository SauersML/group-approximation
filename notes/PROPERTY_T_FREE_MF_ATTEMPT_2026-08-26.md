# Property-`(T)`-free MF collapse: audited state on 2026-08-26

Target:

```text
R=L_(F_2)(1,2),       Delta=St_20(R),       z=x_13(s_1t_1).
```

## Outcome

No Property-`(T)`-free proof of `z in Rad_MF(Delta)` is known in this
snapshot.  The endpoint remains `property-t-free-leavitt-full-mf-radical`
and is `OPEN`.  The established work below consists of reductions, positive
finite-coordinate calculations, and counterexamples fencing invalid
shortcuts.  None may be cited as the radical theorem.

## Exact role of Property `(T)`

Finite-dimensional commutant rigidity itself does not use Property `(T)`.
The manuscript uses it when passing to a norm-matrix corona: the Kazhdan
projection turns the Hilbert--Schmidt asymptotic commutant into a projection
represented inside a stably finite corona, so a one-sided inclusion becomes
equality.  The abstract replacement is false without rigidity; see
`norm-corona-locally-finite-compression-countermodel`.

The separate macroscopic-support use is already Property-`(T)`-free for a
finite-order normal generator.  The exact abstract endpoint is
`torsion-normal-generator-mf-character-criterion`: full
MF radical is equivalent to triviality of every pointwise trace limit of
operator-norm asymptotic representations.  For the literal Steinberg target,
the unresolved instance is
`binary-leavitt-steinberg-mf-characters-are-trivial`.  This formulation uses
normal generation of `z`; it does not assume that the Steinberg central cover
is simple.

## Row-module Fourier reduction

Let the row-one abelian root subgroup be

```text
N={x_(1 bullet)(v):v in R^(19)}
```

and let `H=St_19(R)` be the parabolic actor.  On
`M=hat N=(R^*)^(19)`, a shear `x_jk(b)` sends

```text
lambda_j |-> lambda_j+b.lambda_k
```

and fixes the other coordinates.  Restriction of a character of `Delta` to
`N` gives an `H`-invariant probability measure on `M`.  The established node
`surviving-leavitt-corona-character-has-infinite-parabolic-orbit` is stated
for the last-column convention; its left/right-dual proof applies verbatim
to this row convention and says that the only finite `H`-orbit is `{0}`.  It
does not exclude diffuse invariant measures.  In particular, Haar measure
supplies the regular root profile and satisfies all bounded additive-rank
windows.

The remaining measure route has two logically separate parts:

1. classify ergodic `H`-invariant probability measures on `M`;
2. exclude the Haar/regular profile from restrictions of MF characters of
   the full Steinberg group.

The first statement alone cannot prove MF collapse.

## Rank-integrality audit

For `P_a=(1-rho(x_13(a)))/2`, exact additivity and the conjugacy of the two
depth-one cylinders give

```text
r(1)=2r(q)-2r(P_p P_q),       r(1)<=2r(q).
```

An earlier shortcut asserting `x_13(1)` conjugate to `x_13(q)` is false.
The available four-conjugate saturation gives rank inequalities, not that
equality.  Iterated parity and dyadic divisibility constraints are compatible
with sparse Haar-like rank germs; see
`sparse-dyadic-rank-germ-carries-haar-cyclic-holonomy`.  Hence a bounded
window of integer ranks cannot close the endpoint.

The literal stable Steinberg target also has no available Exel--Loring
shortcut in the audited route: the intended stable `K_2` pairing is empty.
Any central-extension variant must be treated as a distinct target.

## Two concrete firewalls

`norm-corona-locally-finite-compression-countermodel` constructs the Pauli
union in `prod M_(2^n)/directSum_norm` and implements its one-sided shift by
cyclic tensor permutations.  The compressor is strict, its relative
commutant is not normalized, and the scalar defect `-1` survives inside an
amenable corona group.  Therefore amenability or local finiteness cannot
replace Property `(T)` in the generic compression criterion.

`leavitt-diagonal-compression-is-elementary-amenable` locates the same
firewall inside the literal coefficient geometry.  The diagonal subgroup

```text
Lambda=union_k GL_3(F_2)^(2^k)
```

is locally finite, contains `z`, and either single manuscript compressor
produces an elementary amenable group.  Thus diagonal roots plus one
compressor admit an MF model separating `z`.  A load-bearing relation must
use a non-diagonal coefficient occurrence or both complementary compressors.

## Honest surviving targets

The smallest concrete test is the two-compressor subgroup

```text
B=<Lambda,tau,tau'>.
```

Whether `z in Rad_MF(B)` is open.  A positive answer would give the desired
new mechanism and immediately kill `z` in every corona representation of
the ambient group.  A negative answer would force every successful proof to
use off-diagonal coefficients.

The broader alternative is row-dual measure rigidity followed by exclusion
of the Haar MF profile.  These are separate open tasks.  Neither a generic
compression lemma, diagonal one-compressor self-similarity, bounded-window
rank integrality, nor the finite-orbit lemma resolves them.

## Scope firewall

A proof using only normalized Hilbert--Schmidt multiplicativity and excluding
the regular character would prove nonhyperlinearity, not merely non-MF.  A
genuinely MF-specific proof must consume operator-norm/corona structure in a
way unavailable to the regular representation.  Until such a step is proved,
`property-t-free-manuscript-results` and the requested Lean endpoint remain
blocked.
