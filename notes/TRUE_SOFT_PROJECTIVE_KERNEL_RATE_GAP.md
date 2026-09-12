# Tensor sharpening leaves the exact projective kernel maximally wrong

Date: 2026-08-11

## Outcome

The Gaussian/character formulation suggests a tempting TRUE shortcut.
Given `pi:F->U(d)`, quotient by the exact projective kernel

```text
K_pi={g:pi(g) is scalar}.                              (SPK1)
```

The projective image is a finitely generated complex linear group, hence
residually finite by Malcev.  One might hope that tensor powers, which
sharpen the character toward `0/1`, make the regular finite actions of this
projective quotient into the desired sofic models.

This note proves that the shortcut fails in the strongest possible way.
Tensor powers of the conjugate double do not change `(SPK1)`.  For a sofic-radical witness retained
by the matrix model, at least one defining relator lies outside `(SPK1)`.
The tensor character of that relator can tend to one while the regular
character of the projective quotient remains exactly zero.  Hence the two
models remain distance one on a tested relator.

What tensoring does produce is a canonical nested family of **soft
projective kernels** with exact additive threshold closure.  On every fixed
finite window these recover the correct coset equivalence relation.  The
unresolved step is precisely to globalize that local soft equivalence into
a finite stabilizer law; residual finiteness of the exact projective image
does not do so.

## 1. Projective Hilbert--Schmidt length

Let `F` be a finitely generated free group and let

```text
pi:F->U(d),
q_pi(g)=|tr_d(pi(g))|^2.                               (SPK2)
```

Put `rho_pi=pi tensor conjugate(pi)`.  Then

```text
tr_(d^2)(rho_pi(g))=q_pi(g),
delta_pi(g)
 :=2^(-1/2)||rho_pi(g)-I||_(2,d^2)
 =sqrt(1-q_pi(g)).                                    (SPK3)
```

Thus `delta_pi` is a conjugation-invariant, symmetric, subadditive length:

```text
delta_pi(gh)<=delta_pi(g)+delta_pi(h).                (SPK4)
```

Moreover

```text
delta_pi(g)=0
 iff rho_pi(g)=I
 iff pi(g) is scalar.                                 (SPK5)
```

The last equivalence uses equality in
`|tr_d(U)|<=1`: a unitary has normalized trace of modulus one exactly when
all its eigenvalues are equal.  Hence `(SPK1)` is the zero set of
`delta_pi`; it is a normal subgroup.

## 2. Exact soft-kernel calculus

For `t>=0`, define

```text
K_pi(t)={g in F:delta_pi(g)<=t}.                      (SPK6)
```

These sets satisfy

```text
K_pi(0)=K_pi,
K_pi(t)^(-1)=K_pi(t),
h K_pi(t) h^(-1)=K_pi(t),
K_pi(s) K_pi(t) subset K_pi(s+t).                    (SPK7)
```

In particular,

```text
K_pi(t_1)...K_pi(t_L) subset K_pi(t_1+...+t_L).      (SPK8)
```

This is the strongest automatic subgroup-like statement: positive
thresholds add.  A fixed positive threshold is not generally closed under
multiplication.

There is also a left-invariant filtered proximity relation

```text
g approximately_t h  iff delta_pi(g^(-1)h)<=t,       (SPK9)
```

with the exact composition law

```text
approximately_s composed approximately_t
  subset approximately_(s+t).                        (SPK10)
```

It is reflexive and symmetric, but for `t>0` it need not be transitive;
`(SPK10)` is the precise substitute.

If `q_(pi_n)->1_N` pointwise for `N normal F`, then on every fixed finite
window `B subset F` and every fixed `0<t<1`, eventually

```text
delta_(pi_n)(g^(-1)h)<=t
 iff g^(-1)h in N,
g,h in B.                                            (SPK11)
```

Thus the soft kernels recover the exact quotient-coset partition on every
finite window.  This is local information only; every marked group has its
own correct finite multiplication tables.  Finite-index realization of
these tables is the missing global assertion.

## 3. Tensor sharpening

For the amplified representation

```text
sigma_(pi,m)=rho_pi^(tensor m),                       (SPK12a)
```

the normalized character is

```text
q_(pi,m)(g)=q_pi(g)^m,                                (SPK12)
```

and its projective length is

```text
delta_(pi,m)(g)^2=1-(1-delta_pi(g)^2)^m
                 <=m delta_pi(g)^2.                  (SPK13)
```

The exact kernel does not change:

```text
ker(sigma_(pi,m))=K_pi.                               (SPK14)
```

Indeed `q_pi(g)^m=1` if and only if `q_pi(g)=1`.  This is a statement about
the conjugate-double amplification `(SPK12a)`.  The raw tensor power
`pi^(tensor m)` can acquire additional scalar elements and is not being
used here.

Let `R` and `W` be finite relator and witness sets and put

```text
a=max_(r in R)(1-q_pi(r)),
b=max_(w in W)q_pi(w).                                (SPK15)
```

Then

```text
max_(r in R)(1-q_pi(r)^m)<=m a,
max_(w in W)q_pi(w)^m<=b^m.                           (SPK16)
```

For a sequence with `a_n->0` and `b_n->0`, choose for example

```text
m_n=min(n,max(1,floor(a_n^(-1/2)))),                  (SPK17)
```

with the second entry interpreted as `n` when `a_n=0`.

Then

```text
m_n->infinity,
max_R(1-q_(pi_n)(r)^m_n)->0,
max_W q_(pi_n)(w)^m_n->0.                             (SPK18)
```

So tensor amplification gives an extremely sharp normal `0/1` table.  It
still does not make an approximate relator projectively trivial.

## 4. Maximal separation from the exact-kernel regular character

Let

```text
P=<S|R>
```

and let `w in Rad_sof(P)`.  For any representation `pi:F(S)->U(d)`, suppose

```text
w notin K_pi.                                        (SPK19)
```

Then some `r in R` lies outside `K_pi`.

**Proof.**  If every `r` lay in `K_pi`, the conjugate-double representation
`rho_pi` would kill every relator and factor through `P`.  Its image is a
finitely generated complex linear group.  By Malcev it is residually
finite, hence sofic.  Radical membership would force `rho_pi(w)=I`, which
by `(SPK5)` means `w in K_pi`, contradicting `(SPK19)`.  End proof.

The quotient `F/K_pi` is isomorphic to the projective image of `pi`, hence
is also finitely generated linear and residually finite.  Its regular
character is

```text
lambda_pi(g)=1_(K_pi)(g).                            (SPK20)
```

For the relator supplied above,

```text
lambda_pi(r)=0                                       (SPK21)
```

for every amplification `(SPK12a)`, whereas `q_pi(r)^m` may be arbitrarily close to
one.  More precisely, for a sequence satisfying `(SPK18)` and retaining
`w`, choose `r_n in R setminus K_(pi_n)`.  Since `R` is finite, after a
subsequence `r_n=r` is constant, and

```text
|q_(pi_n)(r)^m_n-lambda_(pi_n)(r)| ->1.              (SPK22)
```

Every regular finite quotient of `F/K_(pi_n)` also moves `r` on all points
once that quotient detects `r`.  Thus Malcev residual finiteness supplies
the wrong normalization: it treats a nonzero but microscopically small
projective relator as a full Hamming error.

## 5. Exact remaining possibility

The no-go concerns the regular actions of the exact projective quotient.
It does not rule out nonregular finite actions of that linear group in which
the small relator images lie in most point stabilizers while the witness
does not.  Such actions would require finite-index subgroups `H` with

```text
Prob_x[x^(-1) pi(r) x in H] close to 1,
Prob_x[x^(-1) pi(w) x in H] close to 0.               (SPK23)
```

Constructing `(SPK23)` with bounds controlled by `(SPK3)` is exactly a
metric stabilizer-law theorem, not ordinary residual finiteness.  The
scalar finite metric obstruction already recorded in the notepad shows
that it cannot hold for arbitrary unitary tables without using the normal
endpoint and the fixed word system.

The sharpened conclusion is therefore:

> Tensor powers solve scalar separation but do not exactify relations.
> Exact projective kernels are residually finite but remain discontinuous
> at every nonzero relation defect.  A TRUE proof must round the **soft**
> kernels collectively into finite-index stabilizer laws; it cannot first
> replace them by their exact zero sets.
