# Literal eight-lamp finite-packet holonomy certificate

Date: 2026-08-26.

Let `E` be the literal finitely presented group, with

```text
w = the central Clifford sign,
d = t c t^-1,
u = [d,v_1],
q : E -> H = E/<w>.
```

This note gives a second proof of the hard inclusion

```text
<<u>>^E <= Rad_MF(E),
```

using the fixed eight-lamp packet, its finite character holonomy, and the
common carrier returned through the one-sided compressor.  It does not use
the commuting-involution endpoint that supplied the original proof.

Combined with the independently established MF model of `E/<<u>>`, it gives
the boxed computation

```text
E is finitely presented and sofic,
Rad_MF(E) = <<[tct^-1,v_1]>>^E.                         (L8H0)
```

## 1. The literal finite packet

The block computation for the literal lamp kernel gives

```text
H = (*_(i in I) (C_2)^8) semidirect_product V.
```

Let `L=q(B)` be the image of the literal affine base and let `s=q(t)`.  The
eight conjugates of `q(d)` by representatives of `B/tBt^-1` generate one
embedded block

```text
K ~= (C_2)^8.
```

The following facts are literal relations or conclusions of the block
normal form.

1. `L` is finitely generated and Kazhdan.
2. `sLs^-1 <= L`.
3. `K` is normalized by `L`.
4. `q(d)` is fixed by `sLs^-1`.
5. `q(v_1)` moves `q(d)` to a different basis lamp of `K`.

The action of `L` on the eight basis lamps factors through
`AGL_3(F_2)`.  Dually, it gives a finite permutation holonomy on the 256
characters of `K`.  This is the finite packet used below.

The fifth item is important twice.  It says that the marked commutator is
nontrivial in `H`, and it prevents the certificate from degenerating into the
positive regular profile that survives bare restriction and conjugacy
constraints.

## 2. Exactification and covariance

Fix an arbitrary homomorphism

```text
rho : H -> U(prod_n M_(d_n)(C) / directSum_n M_(d_n)(C)).
```

Tail exactification of the finite subgroup `K` gives exact coordinate
representations

```text
V_n : K -> U(d_n).
```

For a fixed symmetric generating set `S` of `L`, finite averaging and polar
decomposition correct the chosen lifts of `rho(a)`, `a in S`, so that they
implement the exact permutation of the 256 isotypic projections prescribed
by the `AGL_3(F_2)` holonomy.  The correction tends to the identity in
operator norm.  Thus the character projections and all transport maps live
on one authenticated packet carrier; they are not independently chosen
profiles.

Put

```text
b_n(g) = V_n(g d g^-1) - V_n(d),
r_(n,a) = rank b_n(a),
W_n = sum_(a in S) r_(n,a).
```

Because `K` is an elementary abelian two-group, the two exact packet
involutions in any difference are simultaneously diagonalizable.  Every
nonzero singular value of their difference is exactly `2`.  Hence the packet
has the exact integral energy identity for the unnormalized
Hilbert--Schmidt (Frobenius) norm

```text
sum_(a in S) ||b_n(a)||_2^2 = 4 W_n.                  (L8H1)
```

This is the spectral floor that converts the finite character multiplicities
into a rank certificate.

## 3. The common-carrier return

Exact covariance and rank subadditivity give

```text
rank b_n(g) <= |g|_S W_n
```

for every fixed `g in L`.  If the marked displacement survived, pass to a
subsequence with `W_n>=1` and use `W_n` as the weight in the Hilbert
ultraproduct.  The normalized displacement is then a genuine nonzero cocycle
for the adjoint action of `L`.

Property `(T)` makes it a coboundary.  Since `sLs^-1` fixes `d`, its primitive
is fixed by the compressed subgroup.  Pulling that primitive back by `s`
produces an `L`-fixed vector.  The two directions of scaled Kazhdan transport
return this vector through the same packet intersection.  This returned
vector is the common carrier: it is simultaneously the carrier on which the
packet character projections were exactified and the carrier on which the
one-sided compression holonomy closes.

Consequently

```text
sum_(a in S) ||b_n(a)||_2^2 = o(W_n).                 (L8H2)
```

This nonlinear return is the additional row missing from the homogeneous
finite-packet multiplicity calculus.  Mere character tables, restrictions,
and conjugacies would retain the positive regular profile.

## 4. Finite rational terminal certificate

Choose a tail on which the right side of `(L8H2)` is at most `2W_n`.  Together
with `(L8H1)`, the whole terminal calculation is

```text
W_n >= 0,
4 W_n <= 2 W_n,
therefore W_n = 0.                                    (L8H3)
```

Equivalently, introduce a nonnegative slack rank `S_n` and check
`4W_n+S_n=2W_n`; then `2W_n+S_n=0`.  This is precisely a finite rational dual
certificate in the projection-dimension calculus.  It kills every character
multiplicity on which some generator moves `d`.  In particular every
corona homomorphism from `H` kills
`[q(v_1),q(d)]`, and hence also `q(u)` (the two commutator orientations are
inverse-conjugate).

Now let `Theta:E->U(Q)` be arbitrary.  The already formalized central-mark
theorem gives `Theta(w)=1`, so `Theta` factors through `q:E->H`.  The packet
certificate kills `q(u)`, hence `Theta(u)=1`.  Normality of kernels gives

```text
<<u>>^E <= Rad_MF(E).                                  (L8H4)
```

## 5. Exactness and positive properties

Put `D=<<u>>^E`.  Independently of the packet argument, the affine parity
calculation and amalgam normal form give

```text
E/D ~= Sigma *_B (B x C_2).
```

The literal matrix model makes `Sigma` finitely generated linear over `Q`,
hence residually finite.  The right side embeds in the MF symmetric double
`(Sigma x C_2) *_B (Sigma x C_2)`, so `E/D` is MF.  A faithful corona model of
`E/D` has pullback kernel exactly `D`, proving

```text
Rad_MF(E) <= D.                                        (L8H5)
```

Equations `(L8H4)` and `(L8H5)` prove `(L8H0)`.  Finite presentation and
soficity are the unconditional Lean theorems
`LiteralNonMFPresentation.markedGroup_finitelyPresented` and
`LiteralSoficAssembly.markedGroup_isSofic`.

## Trust boundary

* Lean: the literal presentation, finite presentation, property `(T)` input,
  compression relations, sign-free quotient, central-mark annihilation,
  nontrivial unsquared defect, soficity, and the generic scaled Kazhdan
  transport/rank inequalities.
* Established Cairn paper route: finite-packet tail exactification, covariance
  polar correction, weighted cocycle assembly, and the common-carrier return
  in `finite-noncommutative-packet-compression-collapse`.
* Paper-level literal specialization: identification of the eight-lamp packet
  with the level-one block and the quotient-amalgam MF upper bound.
