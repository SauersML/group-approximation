# Iwahori defect has an exact odd-order spectral shadow

Date: 2026-08-14

## 1. Outcome

Let

```text
alpha,beta:SL_2(Z)->U(d)                              (OSS1)
```

be exact representations and put

```text
X=beta(u),                 Y=alpha(l),                 (OSS2)
```

where `u` and `l` are the upper and lower elementary unipotents.  Suppose
the two noncentral Iwahori defects satisfy

```text
||alpha(u)-X^2||_2<=delta,
||beta(l)-Y^2||_2<=delta.                              (OSS3)
```

Then there are unitaries `X_o,Y_o in U(d)` such that

```text
||X-X_o||_2 <=(pi/2)delta,
||Y-Y_o||_2 <=(3pi/2)delta,                            (OSS4)
```

and their eigenvalue multisets satisfy the two exact identities

```text
Spec(Y_o)=Spec(X_o^(-2)),
Spec(X_o)=Spec(Y_o^(-2)).                              (OSS5)
```

Moreover, there is one odd integer `M` such that

```text
X_o^M=Y_o^M=1.                                        (OSS6)
```

Thus every small Iwahori defect is dimension-independently close, at the
level of the two unipotent matrices, to exact odd-order spectral data.  The
two-adic scale escape isolated in
`TRUE_IWAHORI_UNBOUNDEDNESS_IS_CORE_MISALIGNMENT.md` disappears completely
from the empirical spectra.

This is not yet a compatible modular pair.  The optimal eigenvalue
matchings used below need not be implemented by unitaries close to the
actual Weyl elements in `alpha` and `beta`.  Equations `(OSS5)` align
eigenvalue multisets, not the relative spectral flags of `X_o` and `Y_o`.
The remaining Iwahori problem is therefore a flag-alignment problem after
the odd spectral correction, rather than an eigenvalue or two-adic-order
problem.

## 2. Exact conjugacy inside the modular vertices

Let

```text
w=[[0,-1],[1,0]].                                      (OSS7)
```

Direct calculation gives

```text
w u w^(-1)=l^(-1).                                    (OSS8)
```

Consequently

```text
Spec(alpha(u))=Spec(Y^(-1)),
Spec(beta(l))=Spec(X^(-1)).                            (OSS9)
```

For a normal `d`-by-`d` matrix `A`, write `mu_A` for the empirical
eigenvalue measure, with every eigenvalue carrying mass `1/d`.  The
Hoffman--Wielandt matching theorem and `(OSS3)--(OSS9)` imply

```text
W_(2,chord)(mu_(Y^(-1)),mu_(X^2))<=delta,
W_(2,chord)(mu_(X^(-1)),mu_(Y^2))<=delta.             (OSS10)
```

Here the cost is Euclidean chord distance on the unit circle.

Let `J(z)=z^(-1)` and `S(z)=z^2`.  Both `J` and `S` preserve the unit circle,
`J` is an isometry, and `S` is `2`-Lipschitz in chord distance.  Rewriting
`(OSS10)` gives

```text
W_2(mu_Y,(J S)_*mu_X)<=delta,
W_2(mu_X,(J S)_*mu_Y)<=delta.                          (OSS11)
```

Since `(J S)^2(z)=z^4`, the triangle inequality yields

```text
W_2(mu_X,(z |-> z^4)_*mu_X)<=3delta,                  (OSS12)
```

and symmetrically for `mu_Y`.  The next sections use the two couplings in
`(OSS11)` simultaneously, which is stronger than correcting `(OSS12)` twice
independently.

## 3. Two eigenvalue matchings form an approximate fourth-power cycle

List the eigenvalues, with multiplicity, as

```text
x_1,...,x_d for X,          y_1,...,y_d for Y.         (OSS13)
```

Hoffman--Wielandt supplies permutations `a,b` of `{1,...,d}` such that

```text
(1/d)sum_i |y_(a(i))-x_i^(-2)|^2 <=delta^2,
(1/d)sum_j |x_(b(j))-y_j^(-2)|^2 <=delta^2.            (OSS14)
```

Use angular distance on the circle and choose signed errors `e_i,f_j` in
`[-pi,pi]` satisfying

```text
arg(y_(a(i))) = -2arg(x_i)+e_i             mod 2pi,
arg(x_(b(j))) = -2arg(y_j)+f_j             mod 2pi.   (OSS15)
```

For points on the unit circle, angular distance is at most `pi/2` times
chord distance.  Hence, with normalized Euclidean norms on the index set,

```text
||e||_2,||f||_2 <=(pi/2)delta.                         (OSS16)
```

Put

```text
p=b composed a.                                       (OSS17)
```

Substitution in `(OSS15)` gives

```text
arg(x_(p(i)))=4arg(x_i)+g_i                 mod 2pi,
g_i=f_(a(i))-2e_i,                                    (OSS18)
```

and therefore

```text
||g||_2<=3(pi/2)delta.                                 (OSS19)
```

Thus `p` organizes all eigenvalues into finite approximate orbits of the
expanding fourth-power map.

## 4. Dimension-free cycle shadowing

We use an elementary shadowing lemma whose constant does not depend on the
cycle length.

**Lemma 1 (fourth-power cycle shadowing).**  Let `p` be a permutation of a
finite set and suppose angles `theta_i` satisfy

```text
theta_(p(i))=4theta_i+g_i                    mod 2pi.  (OSS20)
```

Then there are angles `phi_i` with

```text
phi_(p(i))=4phi_i                              mod 2pi
```

and

```text
||phi-theta||_2 <=(1/3)||g||_2.                       (OSS21)
```

**Proof.**  On every cycle, extend `g_(p^k(i))` periodically to `k>=0` and
put

```text
r_i=sum_(k>=0) g_(p^k(i))/4^(k+1).                    (OSS22)
```

The geometric series gives

```text
r_(p(i))=4r_i-g_i.                                    (OSS23)
```

Thus `phi_i=theta_i+r_i` satisfies the exact relation modulo `2pi`.
Convolution by the nonnegative kernel `(1/4,1/4^2,...)` has normalized
`l_2` operator norm at most its `l_1` norm

```text
sum_(k>=0)1/4^(k+1)=1/3,                              (OSS24)
```

which proves `(OSS21)` after summing over the disjoint cycles.  End proof.

Apply Lemma 1 to `(OSS18)`.  From `(OSS19)--(OSS21)`,

```text
||phi-arg(x)||_2 <=(pi/2)delta.                        (OSS25)
```

Define corrected eigenvalues by

```text
x_i^o=exp(i phi_i),
y_(a(i))^o=(x_i^o)^(-2).                              (OSS26)
```

Chord distance is at most angular distance, so `(OSS25)` proves the first
bound in `(OSS4)`.  Equations `(OSS15)`, `(OSS16)`, and `(OSS26)` give

```text
||arg(y^o)-arg(y)||_2
 <=2||phi-arg(x)||_2+||e||_2
 <=(3pi/2)delta,                                      (OSS27)
```

which proves the second bound.

The first identity in `(OSS5)` is the definition of `y^o`.  For
`j=a(i)`, equations `(OSS17)`, exact shadowing, and `(OSS26)` give

```text
x_(b(j))^o=x_(p(i))^o=(x_i^o)^4=(y_j^o)^(-2).         (OSS28)
```

Since `a` and `b` are permutations, `(OSS28)` proves the second identity in
`(OSS5)`.

Finally, if `i` lies on a `p`-cycle of length `L`, exact shadowing gives

```text
(x_i^o)^(4^L)=x_i^o,
(x_i^o)^(4^L-1)=1.                                    (OSS29)
```

The number `4^L-1` is odd.  Taking the least common multiple over the
finitely many cycles produces an odd `M` annihilating every `x_i^o` and,
by `(OSS26)`, every `y_j^o`.  This proves `(OSS6)`.

Choose eigenbases for `X` and `Y` and replace their diagonal eigenvalues by
the corrected lists.  This constructs the matrices `X_o,Y_o` and completes
the proof.

## 5. What the theorem removes

The spectral part of a putative negative Iwahori sequence can no longer use:

1. eigenvalues of genuinely unbounded two-power order;
2. empirical spectral mass drifting along an open fourth-power tower;
3. a mismatch between the two inverse-square eigenvalue multisets; or
4. a dimension-dependent shadowing constant on long spectral cycles.

All four are corrected in the original dimension with an explicit linear
bound in the Iwahori defect.  In particular, the expanding nature of
`z |-> z^4` helps: the inverse branches contract by `1/4`, producing the
uniform `1/3` in `(OSS21)`.

## 6. The exact surviving gate is flag alignment

Let `A=alpha(w)` and `B=beta(w)`.  Before correction, `(OSS8)` gives

```text
A Y^(-1) A^*=alpha(u) approximately X^2,
B X^(-1) B^*=beta(l) approximately Y^2.               (OSS30)
```

After `(OSS4)--(OSS5)`, the corresponding pairs of normal matrices have
exactly the same eigenvalue multisets.  Therefore some exact conjugating
unitaries exist.  What has not been proved is that they can be chosen close
in normalized Hilbert--Schmidt norm to the particular unitaries `A` and
`B`, simultaneously with the remaining modular relations.

Hoffman--Wielandt turns matrix closeness into an optimal eigenvalue
permutation.  It does not say that the resulting permutation matrix is
close to the original conjugator.  When many distinct odd roots are very
close, a conjugator can spread mass among their eigenspaces at small matrix
cost while remaining far from every exact block permutation.  No uniform
spectral gap separates those roots because the odd exponent `M` may grow
with `d`.

Thus the corrected target is now:

> **Odd flag-alignment theorem.**  For pairs `(X,Y)` coming from opposite
> exact modular vertices and satisfying `(OSS3)`, promote the exact
> odd-order multiset shadow `(X_o,Y_o)` to nearby matrices for which both
> modular vertex relations and both Iwahori identifications hold exactly.

This is narrower than the original Iwahori question.  Eigenvalue transport,
two-adic conductor drift, and long-cycle shadowing are already solved; only
the relative position of the finite odd spectral flags remains.
