# An exact 24-dimensional omega-sector model of the minimal Kassel four-cell

The determinant calculation in
`kassel-four-cell-is-minimal-determinant-holonomy` locates the first mixed
scalar cycle at Kassel (2.4), (2.5), (2.6), and (2.12).  This note gives an
exact finite-dimensional countermodel to any claim that those four relations
already have positive Maslov energy.

Put `omega=exp(2 pi i/3)`,

```text
nu = exp(-pi i/6),       q = nu^(-2) = exp(pi i/3).
```

## The four-point permutation packet

On `{0,1,2,3}`, compose permutations from right to left and set

```text
a = (2 3),
b = (0 2)(1 3),
d = (0 1)(2 3),
A = (1 3 2),
c = 1.
```

Direct permutation multiplication gives

```text
[a,b]=d,       d^2=1,       b^2=1,       [d,A]=b=b^(-1).   (P)
```

Let `P_g` denote the permutation matrix of `g` on `C^4`.

## The six-point Weyl packet

On the standard basis `e_j`, `j in Z/6`, of `C^6`, define

```text
X e_j = e_(j+1),       Z e_j = q^(-j) e_j.
```

Then

```text
[X,Z]=q I_6.                                             (W)
```

## The root-generator assignment

On `H=C^4 tensor C^6`, assign the six generators occurring in the four
relations by

```text
x_alpha             = P_a tensor X,
x_beta              = P_b tensor I,
x_(alpha+beta)      = I,
x_(2alpha+beta)     = P_d tensor I,
x_(-alpha)          = P_A tensor I,
x_(-beta)           = nu I,
x_(-(alpha+beta))   = I tensor Z.
```

The unused generator `x_(-(2alpha+beta))` may be assigned arbitrarily.
Using `(P)` and `(W)`:

```text
(2.4)  [x_alpha,x_beta]
       = P_d tensor I
       = x_(alpha+beta) x_(2alpha+beta);

(2.5)  [x_alpha,x_(alpha+beta)]
       = I
       = x_(2alpha+beta)^2;

(2.6)  [x_alpha,x_(-(alpha+beta))]
       = q I
       = (nu I)^(-2)
       = x_(-beta)^(-2);

(2.12) [x_(2alpha+beta),x_(-alpha)]
       = P_b tensor I
       = x_(alpha+beta)^(-1) x_beta^(-1).
```

Thus all four mixed-cell relators hold exactly.  On the other hand,

```text
w_beta
 = x_beta x_(-beta)^(-1) x_beta
 = nu^(-1) P_b^2 tensor I
 = nu^(-1) I,

w_beta^4 = nu^(-4) I = omega I.                          (M)
```

This is an exact `24`-dimensional nontrivial marked model.

## Consequence

No inequality of the form

```text
||w_beta^4-I||_2^2
 <= C sum_(i in {2.4,2.5,2.6,2.12}) ||R_i-I||_2^2
```

can hold for all matrix tuples, for any finite `C`: the right side vanishes
on this model while the left side is `|omega-1|^2=3`.

The construction also explains the determinant compatibility.  Its dimension
is divisible by three, so `det(omega I_24)=1`.  The permutation packet solves
the nonlinear transport faces (2.4), (2.5), (2.12), while the independent
six-clock supplies exactly the scalar commutator required by (2.6).  Hence
the four determinant faces do not synchronize into one positive Gram cycle.
Any surviving local atlas must add at least one further relation that couples
these two tensor factors.

