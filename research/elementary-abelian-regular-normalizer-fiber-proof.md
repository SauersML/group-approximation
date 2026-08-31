---
rg: 2
id: elementary-abelian-regular-normalizer-fiber-proof
kind: route
title: Split the free lamp orbits and insert a coherent Fourier multiplicity cocycle
target: elementary-abelian-regular-normalizers-have-diffuse-fibers
requires: []
---

## Step 1: almost every point is in a free orbit

Put

```text
V_n^fr={x in V_n : Stab_B(x)={0}}.
```

Because `B` is fixed,

```text
V_n - V_n^fr = union_(0!=b in B) Fix(sigma_n(b)),
```

and hence `(EAR1)` gives

```text
|V_n-V_n^fr|/|V_n|
 <=sum_(0!=b in B) |Fix(sigma_n(b))|/|V_n| -> 0.        (EAP1)
```

The free set and its complement are both `B`-invariant.  Choose one
basepoint `x_i` in every free orbit.  Define

```text
P_n(h)(sigma_n(b)x_i)=sigma_n(alpha_h(b))x_i            (EAP2)
```

on the free set, and define `P_n(h)` to be the identity on the complement.
Freeness makes `(EAP2)` well-defined.  The homomorphism law for `alpha`
gives `P_n(h)P_n(k)=P_n(hk)` on every free orbit, and it is also true on
the complement.  Thus `P_n` is a genuine permutation representation of
`H`.

Covariance is exact on `V_n^fr`.  Its possible disagreement set on the
complement has measure bounded by the left side of `(EAP1)`, which proves
`(EAR3)`.  Notice that the construction used only the regular-character
condition; no choice of unitary implementers entered.

## Step 2: classify the exact unitary implementers

On `ell^2(B) tensor C^k`, let `P_alpha` be the canonical permutation of
the first factor.  Suppose `U` satisfies `(EAR4)`, and put

```text
D=U(P_alpha tensor 1)^*.
```

For every `c in B`,

```text
D (lambda_B(c) tensor 1) D^*
 =U (P_alpha^* lambda_B(c) P_alpha tensor 1) U^*
 =U (lambda_B(alpha^(-1)(c)) tensor 1) U^*
 =lambda_B(c) tensor 1.
```

Thus `D` is in the lamp commutant and `U=D(P_alpha tensor 1)`.
Uniqueness and the converse are immediate.

If `U_h=D_hP_h` is a genuine actor representation, with tensor identities
suppressed, then

```text
D_(hk)=D_h Ad(P_h)(D_k).                                  (EAP3)
```

So actor multiplication controls the multiplicity freedom only by the
ordinary nonabelian cocycle equation.  It does not force `D_h=1`, or even
force `D_h` to be near a monomial.

## Step 3: an increasing trace-faithful coherent model

Give `F_2^4` a basis `e_0,e_1,e_2,e_3`, and let

```text
J e_i=e_(i+1 mod 4).                                      (EAP4)
```

Thus `J` has order four and, importantly, it permutes the four coordinate
lamps rather than mixing them linearly.  Let

```text
A=direct_sum_(r>=1) F_2^4,
B_m=direct_sum_(r=1)^m F_2^4,
```

and let `C_4=<t>` act blockwise by `J`.  Equivalently, the lamp site set
is `N times (Z/4)` and `t` cyclically permutes the second coordinate.
Truncation `p_m:A -> B_m` is `C_4`-equivariant.

Let `Q_m delta_b=delta_(Jb)` on `ell^2(B_m)`.  For any sequence
`k_m -> infinity`, let `F_(k_m)` be the normalized discrete Fourier
matrix and set

```text
U_m=Q_m tensor F_(k_m).
```

The standard identities `F_k^2 e_r=e_(-r)` and `F_k^4=1`, together with
`Q_m^4=1`, give `U_m^4=1`.  Moreover,

```text
U_m (lambda_(B_m)(b) tensor 1) U_m^*
 =lambda_(B_m)(Jb) tensor 1.                              (EAP5)
```

Consequently

```text
pi_m(a,t^j)
 =(lambda_(B_m)(p_m(a)) tensor 1) U_m^j                  (EAP6)
```

is an exact representation of the fixed group `A rtimes_J C_4`.  It
factors through `B_m rtimes_J C_4`.  Formula `(EAP5)` proves zero
lamp-covariance defect, and `U_m^4=1` proves exact actor coherence.

These representations have the canonical group trace.  If `j=0` and
`a!=0`, then `p_m(a)!=0` for all sufficiently large `m`, and its left
translation has trace zero.  For `j=1,3`, every diagonal entry of
`F_(k_m)^j` has modulus `k_m^(-1/2)`, so

```text
|tr_(k_m)(F_(k_m)^j)| <= k_m^(-1/2).                    (EAP7)
```

The permutation `F_(k_m)^2` has at most two fixed basis vectors, and hence

```text
|tr_(k_m)(F_(k_m)^2)| <= 2/k_m.                         (EAP8)
```

For `j!=0`, the normalized trace of `(EAP6)` is the product of the
normalized traces of `lambda_(B_m)(p_m(a))Q_m^j` and `F_(k_m)^j`.  The
first factor has modulus at most one, while `(EAP7)`--`(EAP8)` tend to
zero.  Thus every fixed nonidentity element has limiting trace zero.

## Step 3b: the actor may be Kazhdan

Let `K=SL_3(Z)`.  This group is residually finite and has property `(T)`.
Choose finite quotients `q_m:K -> L_m` which separate every fixed
nonidentity element eventually; passing to cumulative products gives such a
single sequence.  Put `H=K times C_4`.  It is again residually finite and
Kazhdan, and let it act on `A` through the second factor.

On

```text
H'_m=ell^2(B_m) tensor ell^2(L_m) tensor C^(k_m)
```

define

```text
pi'_m(a,g,t^j)
 =(lambda_(B_m)(p_m(a)) Q_m^j)
  tensor lambda_(L_m)(q_m(g))
  tensor F_(k_m)^j.                                     (EAPK1)
```

The three factors show directly that `pi'_m` is an exact representation of
`A rtimes H` and implements the prescribed lamp automorphism.  Its lamp
restriction is `|L_m|k_m` copies of the regular `B_m`-action.

The trace is canonical.  A nontrivial surviving lamp translation has trace
zero.  If the `K`-coordinate is nontrivial, its eventually nontrivial left
translation on `L_m` has trace zero.  If the `C_4`-coordinate is
nontrivial, `(EAP7)--(EAP8)` make the Fourier trace tend to zero.  These
three cases exhaust the nonidentity elements.  For the actor element `t`,
the matrix

```text
Q_m tensor 1_(ell^2(L_m)) tensor F_(k_m)
```

still has exactly `k_m` entries of modulus `k_m^(-1/2)` in every row.
Consequently the distance and padding estimates below hold verbatim with
`d'_m=|B_m||L_m|k_m`.  Thus even an infinite residually finite Kazhdan
actor does not remove the coherent Fourier multiplicity fiber.

## Step 4: the sharp monomial distance, including padding

In the product lamp basis, every row of `U_m=Q_m tensor F_(k_m)` has
exactly `k_m` nonzero entries, all of modulus `k_m^(-1/2)`.  A monomial
matrix selects at most one entry in each row.  With
`d_m=|B_m|k_m`, it follows that for every monomial `M_m`,

```text
|tr_(d_m)(M_m^* U_m)| <= k_m^(-1/2).                    (EAP9)
```

Both matrices are unitary, so

```text
||U_m-M_m||_(2,d_m)^2
 =2-2 Re tr_(d_m)(M_m^*U_m)
 >=2-2/sqrt(k_m),
```

which is `(EAR8)`.

This persists under every negligible block padding, not just identity
padding.  Let `r_m=o(d_m)`, let `Z_m in U(r_m)` be arbitrary, and compare
`U_m direct_sum Z_m` with an arbitrary monomial `M'_m` of size
`d_m+r_m`.  The old rows contribute at most `d_m/sqrt(k_m)` to the
unnormalized overlap and the new rows contribute at most `r_m`.
Cross-block choices contribute zero.  Hence

```text
|tr_(d_m+r_m)((M'_m)^*(U_m direct_sum Z_m))|
 <=(d_m/sqrt(k_m)+r_m)/(d_m+r_m) -> 0.                 (EAP10)
```

Therefore the squared normalized Hilbert--Schmidt distance is at least
`2-o(1)`, and the distance tends to `sqrt(2)`.  This covers every
permutation, every orbit-coherent permutation, and every monomial
representative after `o(d_m)` padding.

Finally, Fourier transform on the `B_m` coordinate decomposes the regular
representation into its characters, each with multiplicity `k_m`.  Thus

```text
(lambda_(B_m)(B_m) tensor 1)'
 isomorphic_to direct_sum_(chi in dual(B_m)) M_(k_m)(C).
```

The subalgebra `1 tensor M_(k_m)` has a diffuse tracial ultraproduct because
`k_m -> infinity`, and `1 tensor F_(k_m)` is precisely the nonclassical
factor of `U_m`.  The obstruction is therefore a macroscopic diffuse
multiplicity cocycle.

For comparison with the published frontier: Kun--Thom Theorem 4.1
(arXiv:2608.06222v1) obtains normalization inside a permutation ultraproduct
from finite expander-component groupoids.  Alekseev--Thom Open Problem 6.2
(arXiv:2608.05362v1) asks whether Kazhdan commutants in tracial matrix
ultraproducts admit finite-coordinate descriptions.  The diffuse algebra
above explains why the finite-window lamp calculation supplies neither
coordinate structure nor the moving-window compatibility needed by those
results.  It is not a counterexample to either published statement.
