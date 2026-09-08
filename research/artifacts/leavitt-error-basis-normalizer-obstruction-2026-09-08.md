# A uniform exclusion of blockwise error-basis-normalizing 24k models

Date: 2026-09-08. Continuation of
`research/artifacts/leavitt-24k-relative-unitary-reduction-2026-09-08.md`.

**Status: a proved restricted obstruction. Hyperlinearity of the binary
Leavitt unit group remains open, and nothing here decides it.**

The result excludes models built from arbitrary direct sums of finite
Pauli/Clifford normalizers, and more generally from normalizers of any
complete finite unitary error basis with group labels, together with
everything within a fixed normalized-Hilbert--Schmidt distance of that
class. Block count and block dimensions may grow without bound. It does
not exclude arbitrary unitary tuples, and Section 7 states the missing
step exactly.

Notation follows the reduction artifact: `tr_d = d^-1 Tr`,
`||A||_(2,d)^2 = tr_d(A^*A)`, group commutator `[a,b]=aba^-1b^-1`,
additive commutators written out. `T` denotes the unit circle.

## 1. A sharp trace gap for error-basis normalizers

A **group-labelled unitary error basis** of `M_d(C)` is a family
`(W_a)_(a in A)` with `A` a finite group of order `d^2` and

```text
W_e = I,   tr_d(W_a^* W_b) = delta_(ab),   W_a W_b in T W_(ab).   (1)
```

These are an orthonormal basis of `M_d` for the normalized-trace inner
product. Their unitary normalizer is

```text
N(W) = { U in U(d) : U W_a U^* in T W_(sigma(a))
                     for some permutation sigma }.
```

**Lemma 1.** `N(W)/T I` is finite, and every nonscalar `U in N(W)` obeys

```text
|tr_d(U)| <= 1/sqrt 2,      ||U-I||_(2,d)^2 >= 2 - sqrt 2.        (2)
```

*Proof.* Orthogonality makes the basis lines distinct, so the
multiplication rule in (1) forces `sigma` to be an automorphism of `A`:
writing `U W_a U^* = xi(a) W_(sigma(a))`, conjugating `W_a W_b` two ways
gives `sigma(ab) = sigma(a) sigma(b)`.

Conjugation by `U` is a linear operator on the `d^2`-dimensional space
`M_d`. Its trace, computed in the matrix-unit basis after diagonalizing
`U`, is `sum_(i,j) lambda_i conj(lambda_j) = |Tr(U)|^2`. Computed in the
orthonormal basis `(W_a)` it is `sum_a tr_d(W_a^* U W_a U^*)`. So

```text
|Tr(U)|^2 = sum_(sigma(a)=a) xi(a).                               (3)
```

If `sigma != id`, its fixed points form a proper subgroup of `A`, of
order at most `d^2/2`, and (3) gives `|Tr(U)|^2 <= d^2/2`.

If `sigma = id`, multiplying two basis elements gives
`xi(ab) = xi(a) xi(b)`, so `xi` is a character of `A`. A nontrivial
character sums to zero, so `Tr(U) = 0`. If `xi = 1` then `U` commutes
with a spanning set of `M_d` and is scalar, which is excluded.

That proves the trace bound, and
`||U-I||_(2,d)^2 = 2 - 2 Re tr_d(U)` gives the norm bound. For
finiteness, `U -> sigma` has finite image in `Aut(A)`; on its kernel `U`
is determined modulo scalars by the character `xi`, and there are
finitely many characters. QED

**The constant is sharp.** In `d=2` with the Pauli basis `I,X,Y,Z` and
`S = diag(1,i)`, direct multiplication gives `SXS^* = Y`, `SYS^* = -X`,
`SZS^* = Z`, so `S` is a nonscalar normalizer with `sigma` of order two
and fixed subgroup `{I,Z}` of index two. Then `Tr(S) = 1+i` and
`|Tr S|^2 = 2 = d^2/2`, meeting (3) with equality, and

```text
tr_2(e^(-i pi/4) S) = 1/sqrt 2,
||e^(-i pi/4) S - I||_(2,2)^2 = 2 - sqrt 2.
```

Write `gamma = sqrt(2 - sqrt 2)` from now on.

## 2. The model class

Call a four-tuple `Y = (Y_c, Y_1, Y_2, Y_3)` in `U(D)` **blockwise
error-basis normalizing** if there is one orthogonal decomposition

```text
C^D = directSum_(j in J) H_j                                      (5)
```

preserved by all four, and on each `H_j` a basis as in (1) whose
normalizer contains all four restrictions. Decomposition, labelling
group, and block dimensions all depend on the tuple, with no bound on
their number or size, and arbitrary scalar phases are allowed in each
block.

This class contains the finite Pauli/Clifford normalizers, their direct
sums, and identity tensor padding. For padding, a basis exists in every
dimension `m`: the shift `X` and clock `Z` with `ZX = e^(2 pi i/m) XZ`
give `X^a Z^b` indexed by `(Z/m)^2`, orthogonal because a nontrivial
shift has zero diagonal and a nontrivial clock sums a geometric
progression to zero; and `U (x) I_m` normalizes a tensor product basis
whenever `U` normalizes the first factor.

Write `C_D` for this class and, for a four-tuple `X`,

```text
delta(X) = inf_(Y in C_D) max_g ||X_g - Y_g||_(2,D).              (6)
```

Only the ordinary normalized-Hilbert--Schmidt distance appears. No
closedness of `C_D` is used, since (6) is an infimum.

## 3. A finite consequence of the MF obstruction

Let `q : P = C_3 * C_2^3 -> H` be the surjection of
`binary-leavitt-units-generated-by-c3-and-c2-cubed`, with
`c` the 3-cycle and `b_1 = x_12(s_0)`, `b_2 = x_12(t_0)`,
`b_3 = x_12(v)`, `v = s_0 t_1 + s_1 t_0`.

**Lemma 2.** There is a finite `T` contained in `ker q` such that every
homomorphism `theta : P -> Q` to a finite group with `theta(T) = 1` has
`theta(c) = 1`.

*Proof.* Otherwise exhaust the countable `ker q` by finite sets `T_n`
and pick finite `Q_n` with `theta_n(T_n) = 1` and `theta_n(c) != 1`.
Compose with the left regular representations of the `Q_n`. Every word
of `ker q` is eventually the identity, so the induced homomorphism into
the unitary group of `prod_n M_(|Q_n|)(C) / {(a_n) : ||a_n|| -> 0}`
kills `ker q` and factors through `H`. It is nontrivial: `theta_n(c)`
has order three, and left translation by an order-three element is
fixed-point-free, so the regular unitary has all three cube roots of
unity in its spectrum and `||lambda(theta_n(c)) - I||_op = sqrt 3`. The
image is a subgroup of the unitary group of a norm matrix corona, so it
is MF, contradicting `binary-leavitt-all-ranks-full-mf-radical`. QED

This proves `T` exists. It identifies none of its words and gives no
bound on their length. Every constant below is explicit once a `T` is
supplied; only positivity is proved here.

## 4. The commutator that cannot vanish

Use the kernel word of `leavitt-24k-first-relation-has-exact-finite-model`:

```text
d = [b_2, c b_1 c^-1],   a = [d, c^-1 d c],   b = c d c^-1,
z = a b a^-1,            r_* = z c z c,                            (8)
```

with images `x_13(1), x_12(1), x_21(1), (12), 1` in `H`. Note
`c^-1 d c = c^2 d c^-2` because `c^3 = 1`, so (8) is the same word as the
one displayed in that claim, in a different spelling. Adjoin `r_*` to
`T`.

For an exact `P`-tuple `X = (C,B_1,B_2,B_3)` with `tr_D(C^2) = 0` --
which includes every regular-factor `24k` tuple, since there `C` is a
multiple of the regular representation of `C_3` -- set

```text
epsilon = max_(r in T) ||r(X) - I||_(2,D).                        (10)
```

Then

```text
||d(X) - I||_2 >= (sqrt 2 - epsilon)/2.                           (11)
```

**This bound is not new.** It is exactly the necessary bound `(LR2)` of
the established claim `leavitt-24k-first-relation-has-exact-finite-model`,
which is consumed here rather than reproved. Its one-line derivation:
`z`, `b`, `d` are conjugate in the free group so their evaluated
distances from `I` agree; telescoping gives
`||z(X) C z(X) C - C^2||_2 <= 2||d(X)-I||_2`; and `||C^2 - I||_2 =
sqrt 2` while `||r_*(X)-I||_2 <= epsilon`.

## 5. The uniform obstruction

Let `R_P` be the seven internal relators `c^3`, `b_i^2`, `[b_i,b_j]`.
Fix word representatives of `T` and put

```text
S = T union R_P,   M = |S|,   L = max(8, max_(r in S) |r|),
A_0 = 1/2 + 2 sqrt M / gamma,
B_0 = 12 + 2 L sqrt M / gamma.                                    (12)
```

**Theorem 3.** Every exact `P`-tuple with `tr_D(C^2) = 0` satisfies

```text
A_0 epsilon + B_0 delta(X) >= 1/sqrt 2.                           (13)
```

So any sequence of regular-factor `24k` models whose `T`-defects tend to
zero has

```text
liminf delta(X) >= 1/(sqrt 2 B_0) > 0.                            (14)
```

*Proof.* Fix `Y in C_D` and put `delta = max_g ||X_g - Y_g||_(2,D)`. A
word of length `l` moves by at most `l delta`, so for every `r in S`

```text
||r(Y) - I||_2 <= epsilon + L delta,                              (15)
```

with the `epsilon` term absent for the internal relators, which `X`
satisfies exactly.

Call a block **bad** when some `r in S` is nonscalar on it. Blockwise
restrictions of `Y` lie in the block normalizer, which is a group, so
Lemma 1 gives each such restriction squared distance at least `gamma^2`
inside its block. Since
`||A||_(2,D)^2 = sum_j (d_j/D) ||A_j||_(2,d_j)^2`, the bad-block weight
`beta` obeys

```text
gamma^2 beta <= sum_(r in S) ||r(Y)-I||_(2,D)^2
             <= M (epsilon + L delta)^2.                          (16)
```

On a good block every word of `S` is scalar, so the four block unitaries
descend to the finite group `N(W_j)/T I`, satisfy all internal relations
of `P`, and kill `T`. Lemma 2 makes the image of `c` trivial, so `Y_c`
is scalar on that block and

```text
d(Y)|_j = [Y_2, Y_1]|_j.                                          (17)
```

Since `[X_2,X_1] = I` exactly and `[b_2,b_1]` has length four,
`||[Y_2,Y_1] - I||_(2,D) <= 4 delta`. Bad blocks contribute at most `4`
each, so

```text
||d(Y)-I||_(2,D)^2 <= 16 delta^2 + 4 beta,                        (18)
```

and with `|d| = 8` and `sqrt(x+y) <= sqrt x + sqrt y`,

```text
||d(X)-I||_2 <= 12 delta + (2 sqrt M / gamma)(epsilon + L delta). (19)
```

Combining (19) with (11) is exactly (13). Take the infimum over `Y`, then
let `epsilon -> 0`, for (14). QED

The proof handles scalar phases rather than assuming they vanish. A word
scalar on a block need not be the identity there; it becomes trivial only
in the projective quotient. Exact commutation of `B_1, B_2` and estimate
(17) are what keep the surviving commutator out of those phases, which is
why selecting a block from a trace-zero generator alone would not
suffice.

## 6. What this says about the group

If `H` is hyperlinear, the reduction artifact supplies regular-factor
models of exactly this shape. Theorem 3 says their four generators must
stay a fixed positive normalized-HS distance from every common blockwise
error-basis-normalizing description, after allowing arbitrary scalar
phases, block dimensions, block counts, tensor padding, and small
perturbations of the whole tuple. So the group cannot acquire hyperlinear
models by replacing finite classical models with ever larger finite
Pauli/Clifford blocks and averaging their defects.

## 7. The unresolved step

**Nothing here proves that unrestricted unitary tuples approach `C_D`.**
Exactifying the two finite subgroup representations separately does not
produce a common complete error basis, or even a common block
decomposition respected by all four generators. Turning Theorem 3 into a
nonhyperlinearity proof needs that recovery assertion for hypothetical
models of this `H`, or a different uniform obstruction covering the
tuples outside `C_D`. Proving hyperlinearity still needs actual models
satisfying every prescribed finite kernel-relation set. Neither is
supplied, and the question is not settled.

Note the direction of that recovery assertion. If `H` is hyperlinear it
is **false**, by Theorem 3 applied to a hyperlinear model sequence. So it
is not a weaker stepping stone toward the gap; it is strictly stronger
than the gap, and a proof of it would be a proof of nonhyperlinearity.
The claim `hyperlinear-leavitt-models-reduce-to-error-basis-normalizers`
records it with that reading attached.

## 8. Independent recheck, and what is new here

Every displayed step above was re-derived rather than read. The three
that carry weight, with verdicts:

* The two computations of the conjugation superoperator trace in (3).
  Correct. The matrix-unit computation needs `U` diagonalized; the
  error-basis computation needs `(W_a)` orthonormal for the normalized
  trace, which is (1).
* The dichotomy on `sigma`. Correct, and the fixed-point set is a
  subgroup precisely because `sigma` is an automorphism, which is itself
  forced by (1). Both branches were checked against the `d=2` example,
  where `sigma != id` attains the bound.
* The block bookkeeping (16) and (18). Correct; both are additivity of
  the unnormalized trace across orthogonal blocks, with the ambient
  normalization unchanged.

The sharpness example was recomputed entrywise: `SXS^* = Y`, `SYS^* =
-X`, `SZS^* = Z`, and `tr_2(e^(-i pi/4)S) = 1/sqrt 2`.

**Delta against the archive.** The note that supplied this argument
records that `clifford-direct-sum-dilution-forces-an-exact-good-block`
already does block selection by trace quantization and a union bound,
and does not claim that principle as new. That is accurate, and the
comparison is worth stating precisely, because the constants differ and
the difference is not an error:

* The existing claim quantizes the distance from a curvature already in
  the normal form `lambda P_a`, `a != 0`, to the block unit scalars, and
  gets squared distance exactly `2`.
* Lemma 1 bounds every **nonscalar element of the full normalizer**,
  a strictly larger class than the basis elements themselves -- the
  phase gate `S` is in it and is not a scalar multiple of any Pauli --
  and its sharp constant is the smaller `2 - sqrt 2`, attained by `S`.
  A larger class must have a weaker gap, and this one is exactly as
  weak as it can be.

The three additions relative to the archive are therefore: the trace gap
for arbitrary group-labelled error-basis normalizers with its sharp
constant and the finiteness of the projective normalizer; stability of
the exclusion under normalized-HS perturbation of the whole tuple, so
that an infimum over a non-closed class still gives a positive bound;
and the use of the MF obstruction, through Lemma 2, to force the
`C_3` generator to be scalar on a good block, which is what makes the
surviving commutator (17) available.

## 9. Provenance and boundaries

The mathematics is a user-supplied note of 2026-09-08, continuing the
`24k` reduction landed the same day. The transcription above adds the
archive comparison of Section 8, the recheck verdicts, the observation
that (11) is an already-established claim rather than a new derivation,
the spelling reconciliation `c^-1 d c = c^2 d c^-2`, and the direction
remark in Section 7.

Two items the supplied note lists as assumed inputs are theorems here,
and are wired as route prerequisites rather than hypotheses: the
identification of the unit group with `EL_3(R)`
(`leavitt-gl-equals-el-and-perfect-unit-group`) and the MF obstruction
(`binary-leavitt-all-ranks-full-mf-radical`). This is the third time an
external note's "supplied inputs" were already established in this
archive; check before accepting such a list.

The supplied note states that it excluded an HS-to-Hamming comparison it
read in `notes/TRUE_FINITE_REGULAR_NORMALIZER_ROUNDING.md`, and used no
rescaling, cocycle, Mautner, metric-substitution or lifting mechanism.
The proof above is consistent with that: it uses only finite-dimensional
linear algebra, the normalized trace, and an exact algebraic quotient.
No such claim about training exposure can be audited here, and none is
made.

Cairn validates the dependency graph. It does not kernel-check this
proof, and no `GroupApproximation/` declaration corresponds to it.
