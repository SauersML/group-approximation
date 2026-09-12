# Two exact countertests for the flexible repair target

Date: 2026-09-08.  Source: an external audit supplied by the user, which
reports no proof of nonhyperlinear existence and instead isolates two
restricted repair formulations and refutes them.  Both calculations were
re-derived here before landing; no code was run (standing order), and the
audit's own numerical checks in dimensions 8, 27, 64 are not reproduced.

The audit is right about its own scope: nothing here produces a nonhyperlinear
group, a uniform Iwahori repair modulus, or an all-dimension certificate.  What
it produces is two proofs that certain *shapes* of repair theorem are
unavailable, one of which contradicts a statement written in this archive.

## 1. Retaining the core can cost a full extra copy of the space

Work in the square-free presentation of `iwahori-square-free-bs14-presentation`
used by `bs14-flexible-cross-packet-boundary-reconciliation`, with the
unnormalized energy `(FBR1)`.  Fix `0 < theta < pi` and put, in any dimension
`d`,

```text
X = I_d,     T = I_d,     R = e^(i theta) I_d.
```

`(R, T)` is an exact `BS(1,4)` representation (`R T R^(-1) = I = T^4`) and `X`
is a unitary, so this is an admissible input.  Its energy has exactly two
nonzero terms, the inversion and the second cubic:

```text
||X^2 - 1||_F^2                  = 0,
||X R X - R^(-1)||_F^2           = d |e^(i theta) - e^(-i theta)|^2 = 4 d sin^2(theta),
||(X T)^3 - 1||_F^2              = 0,
||(X T^2 R)^3 - 1||_F^2          = d |e^(3 i theta) - 1|^2 = 4 d sin^2(3 theta / 2),
```

so `E / d = 4 sin^2(theta) + 4 sin^2(3 theta / 2) = 13 theta^2 + O(theta^4)`,
which tends to zero.

Now suppose an exact completion `(X^, R^, T^)` on dimension `d + k` retains the
old core, i.e. `R^ = R (+) R_new` with the original `R` a reducing summand.
Exactness of `X^2 = (X R)^2 = 1` gives

```text
X^ R^ X^ = R^(-1),
```

so `R^` is unitarily equivalent to its inverse and the multiplicities of
`e^(i theta)` and `e^(-i theta)` in `R^` are equal.  The old summand supplies
`d` copies of the first and none of the second (they are distinct because
`0 < theta < pi`), so `R_new` must supply at least `d` copies of `e^(-i theta)`:

```text
k >= d.
```

Only the involution and inversion relations were used, so no cubic constraint
can remove it, and rationality of `theta / 2 pi` does not help.

Meanwhile the *moving* repair is immediate: replace `R` by `I_d`, obtaining the
trivial tuple, which is exact in the original dimension with displacement
`||R - I_d||_(2,d) = 2 sin(theta / 2) = O(theta)`.

**Consequence for the archive.**  `(FBR1)` asks for an exact tuple on dimension
`d + k` with `k <= C E` and normalized displacement tending to zero; the moving
repair satisfies it with `k = 0`.  The paragraph in the same node introduced by
"Equivalently" asks instead for a multiplicity vector `b` with
`weighted_size(b) <= C E` such that the *old multiplicity data plus b* lies in
the restriction semigroup of exact Iwahori representations.  For this input any
admissible `b` has `weighted_size(b) >= d`, while `C E = 13 C d theta^2 < d`
for small `theta`.  So `(FBR2)` in that reading is false, it is not equivalent
to `(FBR1)`, and `(FBR1)` survives.  The node has been edited accordingly; the
authenticated-family results in its own attempts, which prove `(FBR2)` for
even-Weil packets, are unaffected -- they never see a scalar packet with return
phase off `1`.  The route `gauge-optimized-energy-closes-flexible-boundary`
also survives, because its mechanism moves generators by the square root of the
normalized energy; only its closing citation needed repair.

The general form of the obstruction is now `inverse-conjugacy-padding-equals-multiplicity-defect`:
the least number of dimensions that must be added before a unitary `R` becomes
conjugate to its inverse by an involution is

```text
sum over unordered pairs {lambda, lambda^(-1)}, lambda != +-1, of
    | m_R(lambda) - m_R(lambda^(-1)) |,
```

which is `d` in the example above and can be as large as the dimension.

## 2. Small Hilbert-Schmidt corrections may have to move almost every direction

For `d >= 2` let `zeta = e^(2 pi i / d)` and let `U, V` be the clock and shift,
`U e_j = zeta^j e_j` and `V e_j = e_(j+1 mod d)`.  Then `U V = zeta V U` and

```text
||U V U^* V^* - I||_(2,d) = |zeta - 1| = 2 sin(pi / d) -> 0.
```

Pad arbitrarily: `U_0 = U (+) A`, `V_0 = V (+) B` with `A, B in U(k)`, and let
`U^, V^` be any commuting unitaries on `C^(d+k)`.  With
`Delta_U = U_0 - U^` and `Delta_V = V_0 - V^`,

```text
U_0 V_0 - V_0 U_0 = Delta_U V_0 + U^ Delta_V - Delta_V U_0 - V^ Delta_U,
```

because `U^ V^ = V^ U^`.  The left side is `(zeta - 1) V U (+) (A B - B A)`, of
rank at least `d`, and the right side has rank at most
`2 rank(Delta_U) + 2 rank(Delta_V)`.  Hence

```text
rank(Delta_U) + rank(Delta_V) >= d / 2
```

for every `k`, however large.  In particular a correction of the form
`U^ = e^(i K_U) U_0` with `K_U` supported on the off-diagonal blocks between
the old space and the added one has rank at most `2k`, which forces
`k >= d / 8`.

And yet the pair is repairable in normalized Hilbert-Schmidt norm.  Take
`d = q^3`, split the coordinate cycle into `q` consecutive blocks of length
`q^2`, let `U'` be constant on each block equal to the first clock value there,
and let `V'` be the cyclic shift *within* each block.  Both blocks are
invariant, `U'` is a scalar on each, so `U' V' = V' U'`; and

```text
||U - U'||_(2,d) <= 2 pi / q      (angular variation 2 pi q^2 / d within a block),
||V - V'||_(2,d) = sqrt 2 / q     (exactly q columns change, each by squared norm 2),
```

while `rank(U - U') = d - q`.

**Consequence.**  Small normalized-HS motion and small-rank surgery are
different resources, and the second is strictly weaker: a repair scheme that
only allows corrections supported on the added block plus a sublinear surgery
subspace cannot be the general mechanism.  This does not contradict
`bs14-low-rank-boundary-surgery-preserves-the-regular-face`, which cuts an
already exposed boundary and is a forward operation, not a completeness claim.
Note also the scope: this example is about `Z^2`, which is flexibly
Hilbert-Schmidt stable, so it is evidence about the shape of repair theorems
and about nothing else.  The operator-norm story for the same pair is the
classical Bott/Exel-Loring obstruction already recorded at
`exel-loring-relative-quasirep-invariant`; the bound above is a rank statement
in a regime where HS repair does exist.

## 3. What the audit does not supply

Its own summary is accurate and is repeated here so the graph does not
overstate it.  The Dogon-Vigdorovich implication (flexible HS stability of
`SL_2(Z[1/2])` gives a nonhyperlinear finite central extension) is a published
theorem, and the repair hypothesis it needs is their open Question 1.4.  The
Navier-Stokes moment-repair machinery supplies a right inverse for its own
moment map, not for these relators, and positive covariance decompositions do
not produce vectors coming from a common exact group representation.  The
remaining task is unchanged and is the reverse-authentication step recorded in
`bs14-flexible-cross-packet-boundary-reconciliation`: produce a compatible
exact comparison from an arbitrary approximate input, without assuming one.

Both countertests are consistent with, and were checked against, the earlier
finding of `iwahori-second-order-repair-space-is-empty` from the same day:
repair must move the core, and the directions it moves along cannot be the
first-order-neutral ones at a compatible pair.
