# A property-(T)-free root-kernel theorem, and the countermodel that stops it at the corona

2026-09-08.  Ingestion record for a note reporting a failed attempt on the
`E_4` ring theorem, together with the explicit obstruction it produced.

## First, what the graph already decides

The note's headline is that

```text
R of positive characteristic,  E_4(R) MF   ==>   R directly finite
```

"remains unsettled".  That is true of the note's own argument and false of the
archive: `finite-additive-order-one-sided-defects-are-mf-invisible` establishes
it, for every `n >= 4`, as a special case of the finite-additive-order defect
criterion, using Ershov--Jaikin-Zapirain property (T) for the elementary group
over a finitely generated subring.  So nothing here reopens the ring theorem.

What is live is the **property-(T)-free** version -- the standing obligation
recorded on `property-t-free-jacobson-head-collapse` and its siblings.  Read
against that obligation, the note is a genuine contribution: it supplies a
(T)-free argument that works in finite dimensions, and then proves that the
step needed to carry it to a corona representation is unavailable.

## The valid half: a uniform root-kernel lemma

Let `R` be unital with `mR = 0`, `m >= 2`, let `ts = 1` and `q = 1 - st`, and
put

```text
kappa_m = 2 sin(pi/m).
```

Let `X, Y : (R,+) -> U(d)` be **genuine** additive homomorphisms and
`C, U_s, U_t in U(d)`.  If for every `a in R`

```text
|| C X(a) C* - Y(a) ||        <  kappa_m,                              (U1)
|| [U_b, X(a)] - Y(ba) ||     <  kappa_m     for b in {s,t},           (U2)
```

then `X(qa) = Y(qa) = 1` for every `a`.

The proof is four steps.  A unitary with `u^m = 1` and `u != 1` has an
eigenvalue `omega^k`, `k != 0`, and `|omega^k - 1| = 2|sin(pi k/m)| >= kappa_m`,
so the spectral gap `(U1)` cannot be crossed: `ker X = ker Y =: I`.  The image
of `X` consists of commuting unitaries of order dividing `m`, simultaneously
diagonalisable with entries among the `m`-th roots of unity, hence has at most
`m^d` elements, so `R/I` is a **finite** additive group.  For `a in I`,
`[U_b, X(a)] = 1`, so `(U2)` forces `ba in I`: left multiplication by `s` and
by `t` descends to endomorphisms `S, T` of `R/I`.  Finally `ts = 1` gives
`T S = id`, so `S` is injective, hence bijective on a finite group, so `T` is
its two-sided inverse and `S T = id`, i.e. `sta - a in I` for all `a`.

Two features are worth naming.  `I` is **not** required to be a two-sided
ideal -- invariance under two left multiplications is enough -- so the argument
needs no simplicity and no fullness.  And there is no Kazhdan hypothesis
anywhere.

Applied to an actual finite-dimensional unitary representation `rho` of
`E_n(R)`, `n >= 3`, with

```text
X(a) = rho(e_23(a)),  Y(a) = rho(e_13(a)),  U_b = rho(e_12(b)),
C = rho(w),   w = e_12(1) e_21(-1) e_12(1),
```

the hypotheses hold with error `0`, since `w e_23(a) w^-1 = e_13(a)` and
`[e_12(b), e_23(a)] = e_13(ba)` are exact elementary identities.  So every
exact finite-dimensional unitary representation of `E_n(R)` kills every
`e_ij(qa)`, with no property (T) used.  This is the (T)-free statement the
archive did not have in this form: `finite-root-algebra-forces-steinberg-triviality`
runs the neighbouring argument for exact representations but routes it through
a two-sided ideal and simplicity of the binary Leavitt algebra, and concludes
triviality of the whole representation rather than death of the defect roots.

## The blocking half: the hypotheses are not pointwise obtainable

`(U1)` and `(U2)` are quantified *at one coordinate, for every coefficient*.  A
corona representation supplies the opposite order: *for every fixed
coefficient, at all sufficiently late coordinates*.  The note constructs
explicit finite models over

```text
J = F_2<s,t | ts = 1>
```

showing the exchange fails as badly as it can.

Write `J` in the normal form `s^i t^j` with

```text
(s^i t^j)(s^k t^l) = s^(i + max(k-j,0)) t^(l + max(j-k,0)),
```

let `W_N = span{ s^i t^j : 0 <= i,j < N }` with coordinate truncation
`p_N : J -> W_N`, and put `B_N(b) v = p_N(bv)`.  On the finite set
`Omega_N = W_N (+) W_N` define the involutions

```text
x_N(a)(v,w) = (v, w + p_N(a)),      y_N(a)(v,w) = (v + p_N(a), w),
u_N(b)(v,w) = (v + B_N(b) w, w),    c_N(v,w)    = (w, v),
```

and let `X_N, Y_N, U_N, C_N` be the corresponding permutation unitaries on
`l^2(Omega_N)`.  Then:

* `X_N, Y_N, U_N` are **genuine** additive homomorphisms, and
  `C_N X_N(a) C_N* = Y_N(a)` holds **exactly**, for every `a` and every `N`;
* `[U_N(b), X_N(a)]` is translation of the first coordinate by
  `B_N(b) p_N(a)`, so it equals `Y_N(ba)` **exactly** as soon as `a in W_N` --
  and then for every `b` at once.  Every fixed `a` lies in all large `W_N`;
* the constant Weyl relations hold exactly: `B_N(1) = id`, so `c_N` and
  `u_N(1)` act as `[[0,1],[1,0]]` and `[[1,1],[0,1]]` over `F_2`, giving
  `C_N^2 = 1` and `(C_N U_N(1))^3 = 1`;
* every fixed nonzero coefficient is eventually separated at the maximal
  distance `2`, a nonidentity involution permutation having a `2`-cycle and
  hence a `-1` eigenvector;
* and yet, taking `a_N = s^N`, one has `p_N(a_N) = 0` while
  `t a_N = s^(N-1)` has `p_N(t a_N) = s^(N-1) != 0`, so

```text
X_N(a_N) = 1,      [U_N(t), X_N(a_N)] = 1,     || Y_N(t a_N) - 1 || = 2.
```

Kernel invariance therefore fails **maximally, at every coordinate**, while
every fixed test is eventually exact.  The marked coefficient `q = 1 + st` is
retained throughout: `p_N(q) != 0` for every `N >= 1`, so
`|| X_N(q) - 1 || = 2` always.

In characteristic two the contrast is as sharp as it can be made: the defect of
each fixed test is eventually `0`, not merely small, and the supremum over
coefficients is `2`, the largest distance between unitaries.

## Scope

The models realise only the displayed root relations at the three positions
`(2,3)`, `(1,3)`, `(1,2)`.  They are **not** an approximate representation of
`E_3(J)` or `E_4(J)` -- no image is specified for the root groups into the
third coordinate, and no check of the remaining Steinberg relations is made.
So they are not a counterexample to the ring theorem, which in any case is
established here.  What they refute is the route: obtaining `(U1)`--`(U2)` from
pointwise corona data.

This is a structured instance of the principle already carried by
`corona-defect-is-not-uniform`, which says corona representations have
pointwise but not uniform multiplicativity defect and therefore admit no
Ulam-type stability theorem.  The instance is worth having separately because
its failing hypothesis is not a multiplicativity defect at all -- it is
invariance of a kernel under two left multiplications -- and because it fails
with every multiplicativity test exactly satisfied, which the general principle
does not say.

## Provenance

The note used only the problem's definition of MF and proves its algebra
explicitly; it reports reading five Cairn entries for orientation
(`finite-order-root-cannot-carry-a-corona-bott-class`,
`finite-order-root-corona-bott-proof`,
`finite-root-algebra-forces-steinberg-triviality-proof`,
`corona-representations-have-an-ideal-valued-support-length-proof`,
`window-controlled-finite-dimensional-root-theorem`) and states that the
finite-root-kernel observation in the third motivated the uniform version,
which it then proves rather than assumes.  It reports 40,136 exact `F_2`
checks of the affine formulas for `N = 1..6`, and no proof-assistant
verification.  It searched uniform-stability literature and used none of it.

Re-derived here before landing: the spectral bound `|omega^k - 1| >= kappa_m`,
both directions of `ker X = ker Y`, finiteness of the root image and hence of
`R/I`, the `TS = id => ST = id` step on a finite group, the four-fold
composition giving `[U_N(b), X_N(a)] =` translation by `B_N(b) p_N(a)`, the
normal-form product `t s^N = s^(N-1)`, `p_N(s^N) = 0`, the `2 x 2` matrices
over `F_2` giving `(C_N U_N(1))^3 = 1`, and `p_N(q) != 0` at every `N`.  No
Lean was written or built.
