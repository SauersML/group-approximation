# Finite-core averages cannot uniformly replace the native Kazhdan average

2026-09-08. Written group and finite-trace arguments. No new Lean
verification is claimed. The result tests a proposed approximation
step; it does not decide hyperlinearity.

## 1. Groups, coefficient cores, and tail elements

Put `R=L_(F_2)(1,2)` and identify `H=R^x=GL_4(R)=EL_4(R)`.
Use the native commuting subgroups

```text
L=diag(EL_3(R),1),       K=diag(I_3,R^x).
```

Let `R_d` be the matrix algebra spanned by `s_alpha t_beta` with
`|alpha|=|beta|=d`. Prefix expansion embeds `R_d=M_(2^d)(F_2)` into
`R_(d+1)` by repeating the matrix in the new tail coordinate. Set

```text
F_d=GL_3(R_d)=GL_(3*2^d)(F_2) <= L,
F_infinity=union_d F_d.
```

Choose a fixed unit `q!=1` in `R`, for example the order-three matrix
`[[0,1],[1,1]]` under `R=M_2(R)`. Define

```text
sigma_d(q)=sum_(|alpha|=d) s_alpha q t_alpha,
g_d=diag(sigma_d(q),sigma_d(q),sigma_d(q),1) in H.       (1)
```

The matrix identification `R=M_(2^d)(R)` sends `sigma_d(q)` to
`I_(2^d) tensor q`. Thus `g_d` is nonidentity, lies in `L`, and
commutes with every element of `F_d`. Membership in `L` uses the
established equality `GL_3(R)=EL_3(R)`. In particular `g_d` also
commutes with `F_i` for every `i<=d`.

## 2. The native invariant space and a fixed averaging gap

Let `N=L(H)`, `A=L(L)`, and `B=L(K)` with the canonical traces.
The elementary block calculation gives `C_H(L)=K`: commutation
with the constant elementary matrices makes a commuting matrix block
diagonal with upper block `a I_3`; commutation with every coefficient
root makes `a` central in `R`, and invertibility gives `a=1`.
The lower block is an arbitrary unit of `R`.

The group `L` is infinite simple. Hence any finite conjugation orbit
of `L` in `H` is a singleton: a nontrivial finite permutation action
would inject the infinite simple group into a finite symmetric group.
Square-summable Fourier coefficients constant on conjugation orbits
therefore have support in `K`. Consequently

```text
L^2(N)^(Ad L)=L^2(B),           A' intersect N=B.       (2)
```

Since `g_d` lies in `L\{1}` and `L intersect K={1}`, its canonical
unitary `Y_d=lambda_(g_d)` has `E_B(Y_d)=0`.

The finitely generated ring `R` and the Steinberg property-(T) theorem
give property (T) for `St_4(R)` and its quotient `EL_4(R)`.
The prefix and elementary identifications
`EL_4(R)=GL_4(R)~=R^x~=GL_3(R)=EL_3(R)` transport it to `L`.
Fix a finite symmetric generating set `S` and a Kazhdan constant
`kappa>0`. Define on any exact tracial representation of `L`

```text
T=(1/2) id + (1/(2|S|)) sum_(s in S) Ad(lambda_s).
```

This is a self-adjoint positive bistochastic completely positive
contraction. Its fixed space is the commutant of `L`. Indeed

```text
< (I-T)X,X > = (1/(4|S|)) sum_s ||[lambda_s,X]||_2^2.
```

On the orthogonal complement of the fixed space the right-hand side
is at least `kappa^2 ||X||_2^2/(4|S|)`. Decrease this constant if
necessary and fix `0<gamma<=1/2` with

```text
||T^j X||_2 <= (1-gamma)^j ||X||_2
```

for every such `X`. The gap is independent of the ambient tracial
algebra and of `d`.

## 3. Distance one in every finite extension

Let `N<=Q` be any trace-preserving inclusion of finite von Neumann
algebras. All group elements and averaging maps below are understood
through this inclusion. Write

```text
E=E_(A' intersect Q),
E_d=E_(L(F_d)' intersect Q)
   =(1/|F_d|) sum_(f in F_d) Ad(lambda_f).
```

The closed subspace `L^2(N)` reduces the exact adjoint representation
of `L` on `L^2(Q)`. Hence its invariant projection is the restriction
of the ambient invariant projection. Equivalently `T^j` preserves
`L^2(N)` and converges there to `E_B`, while on `L^2(Q)` it converges
to `E`. It follows that

```text
E(Y_d)=0,       E_d(Y_d)=Y_d,       ||Y_d||_2=||Y_d||op=1.  (3)
```

Since `A' intersect Q` is contained in `L(F_d)' intersect Q`, the
orthogonal projections `E,E_d` are nested. Thus `E_d-E` has
`2->2` norm at most one, and its `infinity->2` norm is also at most
one. Equation (3) attains the bound:

```text
||E_d-E||_(infinity->2)=1.                              (4)
```

The same test unitary and the gap give, for every integer `j>=0`,

```text
||E_d-T^j||_(infinity->2)
 >= ||Y_d-T^j Y_d||_2 >= 1-(1-gamma)^j.                 (5)
```

Any convex adjoint average whose group support is contained in `F_d`
fixes `Y_d`, so (5) applies to it as well. Every finite subset of
`F_infinity` is contained in some `F_d`. Thus changing the finite
weights or increasing a fixed core does not give uniform convergence
on the operator unit ball to the full-left invariant projection.
Canonical regular trace weights on these finite group algebras do
not change (3).

## 4. A single tail unitary in tracial ultraproducts

Suppose in addition that `Q` is a matrix tracial ultraproduct over a
nonprincipal ultrafilter on the natural numbers, or the tracial
ultrapower of the hyperfinite factor. Then there is a unitary `X` in
`Q` such that

```text
[X,lambda_f]=0 for every f in F_infinity,
E(X)=0.                                               (6)
```

Here is the explicit countable-diagonal argument. Enumerate the core
elements. For each finite initial list, choose `d` large enough that
the list lies in `F_d`. The unitary `Y_d` then commutes exactly with
that list and satisfies

```text
||T^j Y_d||_2 <= (1-gamma)^j                           (7)
```

simultaneously for all integers `j>=0`. Lift the countably many
unitaries `Y_d` and the represented generators to unitary sequences
in the coordinate algebras. Such lifts exist by polar decomposition;
the normalized distance to a unitary tends to zero for a lift of a
unitary in the tracial quotient.

For each finite stage choose an ultrafilter-large set of coordinates
where its finitely many commutator and norm conditions hold to the
stage tolerance. Intersect these sets cumulatively and also with
`{n:n>=stage}`. At coordinate `n`, choose the largest available stage
at most `n` and use the corresponding lift of `Y_d`. Use any unitary
when no stage is available. The chosen stage tends to infinity along
the ultrafilter, so the resulting ultraproduct unitary satisfies every
commutator condition and (7) for every fixed `j`.

The powers `T^j` converge in `L^2` to `E`. Since the right side of
(7) tends to zero, this unitary satisfies `E(X)=0`. In particular

```text
dist_2(X,A' intersect Q)=1,
||E_(L(F_infinity)' intersect Q)-E||_(infinity->2)=1.    (8)
```

This applies to every canonical embedding in these ultraproducts if
one exists. It does not assert existence of such an embedding of `N`.

## 5. Finite literal word tests for a proposed matrix replacement

Fix `d,j`. Choose literal native words for `g_d`, all elements of
`F_d`, and the generators in `S`. Evaluate them on any unitary tuple,
writing `Y,W_f,V_s`. Pair inverse spellings in the definition of the
matrix averaging map `T_mat` so it is a lazy symmetric adjoint
average. No exact finite-factor law is assumed here. Put

```text
Phi_d=(1/|F_d|) sum_(f in F_d) Ad(W_f).
```

Suppose the literal commutation rows for `g_d` and `f` give
`||W_f Y W_f^*-Y||_2<=epsilon` for every `f`. Then

```text
||Phi_d(Y)-Y||_2<=epsilon.                             (9)
```

Write the finite convex expansion

```text
T_mat^j(Y)=sum_p mu_p W_p Y W_p^*,      mu_p>=0, sum_p mu_p=1.
```

For every pair `p,q`, assume the trace of the literal word

```text
Y^* W_p^* W_q Y W_q^* W_p
```

differs by at most `eta` from its canonical native group trace.
The expansion of `||T_mat^j(Y)||_2^2` is the weighted sum of exactly
these traces. Since the weights `mu_p mu_q` sum to one, (7) implies

```text
||T_mat^j(Y)||_2^2 <= (1-gamma)^(2j)+eta.
```

Testing on the unitary `Y` and using (9) yields the finite-dimensional
necessary bound

```text
||Phi_d-T_mat^j||_(infinity->2)
 >= (1-epsilon-sqrt((1-gamma)^(2j)+eta))_+.            (10)
```

All tests are finite once `d,j` are fixed. True identity traces are
controlled by their literal kernel rows; the nonidentity traces can
be obtained from the finite single-cycle certificate after adjoining
its rows. If the `W_f` form an exact representation of `F_d`, then
`Phi_d` is its exact commutant expectation. Regular multiplicities
do not remove (10).

## 6. The moving-depth boundary

Equations (4)--(8) concern subgroups and maps in the exact limiting
algebra. Equation (10) concerns coordinate matrices with the displayed
tests imposed at the actual chosen depth. The witnesses `g_d` and
their word-trace tests change with `d`.

If `d=d(n)` grows with matrix size, convergence on every fixed native
word does not by itself give the tests in (10) at depth `d(n)`.
Likewise the ultraproduct of commutants of the full coordinate
representations of `F_(d(n))` need not be the commutant of the
represented fixed union `F_infinity`. The latter always contains
the unitary (6); this does not place that unitary in the former.

Thus the theorem rules out uniform replacement by fixed-core
averaging in an exact canonical embedding, and supplies an explicit
finite test for any proposed matrix replacement. It does not rule
out every suitably chosen growing-core approximation, all other
bounded-distortion algebra approximations, or hyperlinearity of `H`.

There is also a separate obstruction to inferring bounded weights from
the canonical trace and property (T) alone. The explicit
[fixed-group countermodel](kazhdan-canonical-models-with-unbounded-commutant-distortion-2026-09-08.md)
has exact canonical approximations of `SL_3(Z)` whose actual commutant
distortion diverges on two sectors of trace `1/2`, even after deleting
vanishing central trace. This concerns those particular commutants;
it does not rule out all alternative algebra approximations.
