# A surviving recursive head has a tracial core

2026-09-08. This note proves a necessary consequence of a marked
norm-corona representation of the recursive Jacobson candidate. It
does not prove that the marked representation is impossible.

The construction uses finite-group correction, averages of nested
finite-group support projections, spectral coarea, and finite matrix
polar decomposition. It preserves all group relations in normalized
Hilbert--Schmidt norm. No operator-norm conclusion about the compressed
relations is asserted.

## 1. A general support-bound reduction

Let `G` be countable, let `A` be a locally finite normal subgroup, and
let `A_1<=A_2<=...` be a finite subgroup exhaustion of `A`. Fix an
element `a in A_1` of finite order `m>=2`. Suppose `C<infinity` obeys

```text
codim Fix(sigma(A_j)) <= C rank(sigma(a)-I)                 (1)
```

for every `j` and every finite-dimensional complex unitary
representation `sigma` of `A_j`.

**Theorem.** For every homomorphism

```text
rho:G -> U(prod_n M_(d_n) / directSum_n M_(d_n))
```

with `rho(a)!=1`, there are positive integers `k_n` and unitary maps
`W_n:G->U(k_n)` such that

```text
||W_n(g)W_n(h)-W_n(gh)||_(2,k_n) -> 0       (g,h in G),     (2)
W_n(a)^m=I,
rank(W_n(a)-I)/k_n >= 1/C.                               (3)
```

Here `||X||_(2,k)^2=Tr(X*X)/k`. In particular, for any free ultrafilter
the maps define a homomorphism `psi` to the unitary group of a tracial
matrix ultraproduct, with

```text
ker(rho) <= ker(psi),
||psi(a)-1||_2 >= eta_m/sqrt(C),
eta_m=min{|zeta-1| : zeta^m=1, zeta!=1}>0.                (4)
```

The homomorphism need not be faithful on `G`. Nor does the theorem
produce a new operator-norm asymptotic representation in dimensions
`k_n`.

## 2. Nested finite supports

Choose unitary sequence lifts of `rho`, with identity lifted to
identity. Polar decomposition supplies unitary lifts because a lift
of a corona unitary is asymptotically unitary in operator norm. The
lifts `V_n` are therefore operator-norm asymptotic representations.

Restrict to a subsequence on which `||V_n(a)-I||` is bounded below.
A fixed finite-group norm model can be corrected to an exact
representation in its original matrix dimension. This is the
established `finite-group-opnorm-support-profile` theorem; a direct
finite averaging and polar proof is also given in Section 4 of the
[relative correction note](jacobson-boundary-packet-relative-rounding-2026-09-08.md).

We use this only for one finite group at a time. Given a finite
symmetric window `F` in `G` and an integer `N`, normality and local
finiteness give stages in the fixed exhaustion

```text
K_0<=K_1<=...<=K_N,
a in K_0,
g K_i g^(-1)<=K_(i+1)       (g in F, 0<=i<N).             (5)
```

Correct the representation on a stage containing `K_N`. Choose the
coordinate sufficiently late that this correction and every needed
finite covariance error are small. Diagonalize over windows
`F_n` exhausting `G`, integers `N_n->infinity`, and error bounds
tending to zero. This uses no stability constant uniform over the
growing finite groups. After these corrections, still denoted `V_n`,
all fixed ambient multiplication errors tend to zero, and their
restriction to the selected containing group is a single exact
representation `sigma_n`.

Write

```text
p_i=I-|K_i|^(-1) sum_(b in K_i) sigma_n(b),
p_a=1_(C minus {1})(sigma_n(a)),
r_n=rank(p_a)>0,
e_n=N_n^(-1) sum_(i=0)^(N_n-1) p_i.                       (6)
```

The `p_i` are increasing orthogonal projections: their complements
project onto the decreasing fixed spaces. They contain `p_a`.
All groups `K_i` are stages of the fixed exhaustion, so (1) yields

```text
0<=e_n<=I,        e_n p_a=p_a,
rank(e_n)<=C r_n.                                        (7)
```

Exact averaging over the subgroup inclusion in (5), together with
the finite covariance errors, gives, for every `g in F_n`,

```text
V_n(g) p_i V_n(g)* <= p_(i+1)+epsilon_n I,
p_i <= V_n(g) p_(i+1) V_n(g)*+epsilon_n I.                (8)
```

The second inequality uses `g^(-1) in F_n`. Enlarge `epsilon_n`
to cover the inverse-lift errors too. Finite averages have sum of
absolute coefficients one, so no group-order factor is required
once the pointwise covariance errors are bounded uniformly on the
selected finite sets. Sum each inequality for `0<=i<N_n`. Removing
the endpoint projections costs at most `1/N_n`, and hence

```text
||[e_n,V_n(g)]||_op <= 1/N_n+epsilon_n -> 0                (9)
```

for every fixed `g`. These positive cutoffs are constructed entirely
from finite subgroups. We next select actual projections, at the
cost of obtaining only Hilbert--Schmidt control.

## 3. Coarea on the intrinsic rank scale

Let `0<=e<=I` have rank at most `C r`, let `U` be unitary, and put
`q_t=1_[t,1](e)`, for `0<t<=1`. Diagonalizing `e` gives

```text
integral_0^1 ||[q_t,U]||_HS^2 dt
  = sum_(i,j) |lambda_i-lambda_j| |u_ij|^2.               (10)
```

Only pairs for which at least one eigenvalue is nonzero contribute.
The sum of `|u_ij|^2` over those pairs is at most `2 rank(e)`, by
the unit row and column sums of a unitary. Cauchy--Schwarz therefore
bounds (10) by

```text
sqrt(2 rank(e)) ||[e,U]||_HS
  <= 2 rank(e) ||[e,U]||_op
  <= 2 C r ||[e,U]||_op.                                 (11)
```

The middle inequality uses `rank([e,U])<=2 rank(e)`. This is the
same spectral coarea identity as
`covariant-square-function-has-common-reducing-threshold`, with the
contributing rows and columns counted on the active rank scale.
There is no factor depending on the unused ambient dimension.

In the diagonal selection in Section 2, choose the window errors
and `N_n` so that

```text
sum_(g in F_n) ||[e_n,V_n(g)]||_op -> 0.                  (12)
```

For example, first choose `F_n`, then `N_n` much larger than
`n |F_n|`, then make `epsilon_n |F_n|` tend to zero. Sum (11) over
`F_n` and average the threshold over `[1/4,3/4]`. Some `t_n` in
this interval satisfies, for `q_n=q_(t_n)`,

```text
sum_(g in F_n) ||[q_n,V_n(g)]||_HS^2
   <=4 C r_n sum_(g in F_n) ||[e_n,V_n(g)]||_op.           (13)
```

Since `e_n` is identity on `p_a`, while it has rank at most `C r_n`,

```text
p_a<=q_n,       r_n<=k_n:=rank(q_n)<=C r_n.               (14)
```

It follows that `||[q_n,V_n(g)]||_HS/sqrt(k_n)->0` for each fixed
`g`. The projection `q_n` commutes with `V_n(a)` exactly: it is
identity on the nonidentity spectral subspace of this finite-order
unitary, and the unitary is identity on the complementary subspace.

## 4. Polar compression and the kernel inclusion

On `q_n C^(d_n)`, put `X_n(g)=q_n V_n(g) q_n`. For a square
contraction `X`, its singular value decomposition provides a unitary
`W` in the same dimension such that

```text
||W-X||_HS^2=sum_j(1-s_j)^2
   <=sum_j(1-s_j^2)=Tr(I-X*X).                           (15)
```

Zero singular values cause no obstruction: complete the two
orthonormal singular vector lists and pair them. For the compressed
matrix, the last expression in (15) equals

```text
||(I-q_n)V_n(g)q_n||_HS^2.
```

Choose this unitary as `W_n(g)`. If the compression is already
unitary, leave it unchanged; in particular leave `W_n(1)=I` and
`W_n(a)=X_n(a)` unchanged. Equation (13) gives

```text
||W_n(g)-X_n(g)||_(2,k_n) -> 0.                          (16)
```

The exact expansion

```text
X_n(g)X_n(h)-X_n(gh)
 =q_n(V_n(g)V_n(h)-V_n(gh))q_n
   -q_n V_n(g)(I-q_n)V_n(h)q_n                           (17)
```

shows that its normalized Hilbert--Schmidt norm tends to zero. The
first term is bounded by the original operator-norm multiplicative
error; the second is bounded by
`||(I-q_n)V_n(h)q_n||_HS/sqrt(k_n)`. Combining (16)--(17) proves
(2). The eigenvalues of `W_n(a)` away from one are exactly the
`r_n` original nonidentity eigenvalues. Thus (14) proves (3) and
the lower bound in (4).

If `rho(g)=1`, then `||V_n(g)-I||_op->0`, also on the selected
subsequence and after correction. The compression `X_n(g)` tends
to identity in operator norm, and (16) proves `psi(g)=1`. This
establishes the kernel inclusion in (4).

## 5. The recursive Jacobson consequence

For `Gamma=Theta_shift`, the
[full finitary kernel theorem](jacobson-recursive-packets-generate-finitary-linear-kernel-2026-09-08.md)
identifies

```text
L=normalClosure_Gamma(w)=GL_fin(F_2^(Z x {1,2,3})),
w=x_13,Q.
```

It is normal, simple and locally finite. Its standard finite
interval groups satisfy (1) with `C=4`. For clarity, that bound
has a short finite-group proof. In `GL_d(F_2)`, `d>=3`, the row-one
and column-one elementary abelian root groups generate the whole
group. The common Levi group acts transitively on the nonzero
characters of either root group. If their common multiplicity in
one of these restrictions is `b`, then its active dimension is
`(2^(d-1)-1)b`, whereas a designated root moves `2^(d-2)b`
dimensions. The designated roots in the two groups are conjugate,
so their moving ranks agree. Intersecting the two fixed spaces
gives

```text
codim Fix(GL_d(F_2))
  <=(4-2^(3-d)) rank(sigma(w)-I)
  <=4 rank(sigma(w)-I).                                  (18)
```

This works with arbitrary multiplicities and arbitrary trivial
summands; it is the existing
`binary-finitary-transvection-uniformly-controls-active-rank` lemma.

Consequently, any norm-corona homomorphism `rho` retaining `w`
gives a tracial ultraproduct homomorphism `psi` with

```text
rank(W_n(w)-I)/k_n >= 1/4,
W_n(w)^2=I,
||psi(w)-1||_2>=1.                                      (19)
```

Simplicity implies that `psi` is injective on `L`. The
[centralizer calculation](jacobson-recursive-head-dies-in-amenable-targets-2026-09-08.md)
then gives, for the literal representation `pi`,

```text
ker(rho)<=ker(psi)<=C_Gamma(L)=ker(pi).                    (20)
```

Thus the group `psi(Gamma)` is a subgroup of a tracial matrix
ultraproduct retaining `L` and surjecting onto `pi(Gamma)`.
Surjectivity onto `pi(Gamma)` is not a hyperlinear embedding of
that quotient. Elements of `ker(pi)` can still act on multiplicity
spaces in a representation of `L`; the construction does not
remove them.

The new reduction would prove marked norm collapse if one proved
that every tracial matrix-ultraproduct homomorphism of `Gamma`
kills `w`. That tracial-collapse assertion is not proved here.
Alternatively, further information from the original norm models
may be needed. The open objective remains the unrestricted
operator-norm gap in `jacobson-shift-mixed-gap`.

## 6. Verification scope

This is a written proof. Its ingredients are finite-group norm
correction, the elementary support bound (18), nested finite
averages, the rank-sensitive coarea calculation (10)--(13), and
singular value decomposition. The cutoff argument reproduces only
the finite averaging construction from the earlier rank-weighted
note; no transport theorem for an infinite subgroup is used.

The result does not claim a spectral cut almost commutes in
operator norm. In particular, it does not silently replace
Hilbert--Schmidt convergence in (13), (16), or (17) by operator-norm
convergence. Cairn dependency checks and handwritten audits of
these statements are not Lean kernel verification.
