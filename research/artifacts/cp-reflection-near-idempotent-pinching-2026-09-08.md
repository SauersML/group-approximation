# Completely positive reflections round to two-block pinchings

2026-09-08. Written matrix proof. No computation, build, job, or new
Lean verification is asserted.

This gives a quantum special case of mixed-norm expectation rounding.
It assumes that the reflection `2P-id` is itself completely positive.
The proof does not assume that this reflection is already
multiplicative, and it does not bound the Kraus rank of `P`.

Write `tau_d=Tr/d` and `||x||_2=tau_d(x*x)^(1/2)`. All map norms
`infinity->2` test the entire operator unit ball.

## 1. Statement and the reflection defect

Let `P:M_d->M_d` be UCP, trace preserving, and self-adjoint on
`L^2(M_d,tau_d)`. Assume `Q=2P-id` is CP. It is then also unital,
trace preserving, and self-adjoint. Both `P,Q` contract operator
norm and normalized `L^2`. Put

```text
delta=||P^2-P||_(infinity->2),
epsilon=||Q^2-id||_(infinity->2)=4delta.              (1)
```

There is a self-adjoint unitary `V` such that

```text
||P-E_V||_(infinity->2)<=min{2,30sqrt(delta)},
E_V(x)=(x+VxV)/2.                                  (2)
```

For `p=(I+V)/2`, this is the trace-preserving expectation onto
`pM_dp direct_sum (I-p)M_d(I-p)`. Either corner can be zero.

For every unitary `u`, Schwarz and self-adjointness of `Q` imply

```text
0<=tau_d(1-Q(u)*Q(u))
 =1-||Q(u)||_2^2
 =<u,(id-Q^2)u>
 <=epsilon.                                       (3)
```

The middle expression is real, and the upper bound follows by
Cauchy--Schwarz and (1). Thus near-involutivity makes the full source
unitary group nearly unitary after applying `Q`, in normalized trace.

## 2. Full-matrix Stinespring averaging keeps the dimension exact

Assume for now `epsilon<1/2`. Take a finite-dimensional Stinespring
representation

```text
Q(x)=W* pi(x) W,
W:C^d -> K an isometry,       pi:M_d -> B(K) unital,
p=WW*.
```

On the dilation use the trace `tilde_tau=Tr_K/d`, which normalizes
`p`, not the identity of `B(K)`. In a suitable basis,
`pi(M_d)=M_d tensor I_m`. For each source unitary `u`, (3) gives

```text
||[pi(u),p]||_(2,tilde_tau)^2
 =2tau_d(1-Q(u)*Q(u))<=2epsilon.                   (4)
```

Average `p` over the compact group `pi(U(d))`, obtaining
`a=E_(pi(M_d)')(p)`. This is the Hilbert-space orthogonal projection
of `p` onto the commutant. The usual identity for averaging an
isometric group action and (4) give

```text
||p-a||_(2,tilde_tau)^2
 =(1/2) integral_(U(d)) ||p-pi(u)p pi(u)*||_(2,tilde_tau)^2 du
 <=epsilon.                                       (5)
```

Let `q=1_[1/2,1](a)`. Spectral rounding is a nearest projection
to the positive contraction `a` in the Hilbert--Schmidt norm.
In particular `||a-q||_2<=||a-p||_2`. Since `a-q` belongs to
the commutant and `p-a` is perpendicular to it,

```text
||p-q||_(2,tilde_tau)^2<=2epsilon,
|rank(q)/d-1|<=||p-q||_(2,tilde_tau)^2<=2epsilon<1. (6)
```

The rank inequality follows from
`Tr(pq)<=min{Tr(p),Tr(q)}`. Because `q` commutes with
`M_d tensor I_m`, it has the form `I_d tensor q_0`; its rank
is an integer multiple of `d`. Equation (6) therefore forces
`rank(q)=d` exactly. This is the step that removes any change
of matrix dimension.

For equal-rank projections there is an aligning unitary `Z` with

```text
ZqZ*=p,
||Z-I||_(2,tilde_tau)<=sqrt(2)||p-q||_(2,tilde_tau)
                    <=2sqrt(epsilon).             (7)
```

For completeness, decompose the two projection ranges into their
principal-angle two-planes and their common subspace. On a plane
of angle `theta in [0,pi/2]`, a rotation aligning the two lines
has squared Frobenius cost `4(1-cos(theta))`, while the squared
projection distance is `2sin(theta)^2`. The former is at most
twice the latter. Use the identity on their common subspace and
the remaining orthogonal complement, and sum to get (7).

Define

```text
alpha(x)=W* Z q pi(x) q Z* W.
```

Since `q` commutes with `pi(M_d)` and `ZqZ*=p`, this is a unital
*-homomorphism from `M_d` to itself. It is an automorphism, hence
`alpha=Ad(U)` for some unitary `U in M_d`.

For every contraction `x`, comparison before and after the rotation
gives

```text
||p pi(x)p-q pi(x)q||_(2,tilde_tau)<=2||p-q||_(2,tilde_tau),
||Z q pi(x)q Z*-q pi(x)q||_(2,tilde_tau)<=2||Z-I||_(2,tilde_tau).
```

Compression by `W*` and `W` decreases this Hilbert--Schmidt norm.
Using (6)--(7), we obtain

```text
||Q-alpha||_(infinity->2)<=A,
A=(4+2sqrt(2))sqrt(epsilon).                        (8)
```

These estimates use the specified dilation trace throughout. They
do not normalize the whole dilation space to have trace one.

## 3. Near-involutive conjugation gives a matrix involution

All maps being composed here contract both required norms.
The identity

```text
alpha^2-Q^2=alpha(alpha-Q)+(alpha-Q)Q
```

therefore implies

```text
||Ad(U^2)-id||_(infinity->2)<=B,
B=2A+epsilon.                                      (9)
```

Haar averaging over source unitaries `x` gives the exact identity

```text
integral_(U(d)) ||U^2 x U*^2-x||_2^2 dx
 =2(1-|tau_d(U^2)|^2)<=B^2.                        (10)
```

Indeed, Haar conjugation sends any matrix `y` to `tau_d(y)I`.
Choose a scalar `lambda` of modulus one with the phase of
`tau_d(U^2)`; if that trace vanishes, choose any phase. Then

```text
||U^2-lambda I||_2^2
 =2(1-|tau_d(U^2)|)
 <=2(1-|tau_d(U^2)|^2)<=B^2.                       (11)
```

Choose `omega` with `omega^2=lambda`, and put `U_0=omega^(-1)U`.
Spectrally round each eigenvalue of `U_0` to the closer of `+1,-1`,
choosing either sign in a tie. This defines a self-adjoint unitary
`V`. For `z` on the unit circle,

```text
min{|z-1|^2,|z+1|^2}
 =2(1-|Re(z)|)
 <=(1/2)|z^2-1|^2.
```

Equations (11) and this scalar inequality show

```text
||U_0-V||_2<=B/sqrt(2),
||alpha-Ad(V)||_(infinity->2)<=sqrt(2)B.             (12)
```

There is no mixed-norm adjoint interchange in this argument:
(9) uses composition and (10) uses an actual Haar identity.

Since `P=(id+Q)/2`, (8) and (12) give

```text
||P-E_V||_(infinity->2)
 <= A/2+B/sqrt(2)
 = (6+5sqrt(2))sqrt(epsilon)+epsilon/sqrt(2)
 <= (13/2+5sqrt(2))sqrt(epsilon)
 = (13+10sqrt(2))sqrt(delta)
 <=28sqrt(delta).                                 (13)
```

The second inequality uses `epsilon<1/2`. This proves the claimed
`30sqrt(delta)` bound whenever `delta<1/8`, including zero defect.
If `delta>=1/8`, take `V=I`; the distance between two UCP
trace-preserving maps in this norm is at most two. Since
`30sqrt(delta)>2` in that range, (2) follows there as well.
For the small-defect range, the same trivial distance bound applies
to the constructed `E_V`, proving the minimum in (2).

## 4. A larger CP identity component forces the identity expectation

Suppose more strongly that `P-lambda id` is CP for some
`1/2<lambda<1`. Write

```text
P=lambda id+(1-lambda)R,
R=(P-lambda id)/(1-lambda).
```

The map `R` is again self-adjoint, bistochastic and UCP. Its
Hilbert-space spectrum lies in `[-1,1]`, so

```text
spec(P) subset [2lambda-1,1].
```

For every spectral value `s` of `P`,
`|1-s|<=|s-s^2|/(2lambda-1)`. Spectral calculus consequently gives
the pointwise norm inequality, for every matrix `x`,

```text
||(id-P)x||_2<=||(P-P^2)x||_2/(2lambda-1).
```

Taking the supremum over contractions proves

```text
||P-id||_(infinity->2)<=delta/(2lambda-1).            (14)
```

## 5. Scope of the extra hypothesis

The assumption is that `P-(1/2)id` is completely positive as a
map. Nonnegative spectrum of `P` on Hilbert--Schmidt space does
not imply it. For example, the exact diagonal expectation `E_D`
on `M_3` is a positive Hilbert-space projection, but `2E_D-id`
is not positive: applied to the all-ones positive matrix it gives
the matrix with diagonal entries one and off-diagonal entries minus
one, whose eigenvalue on the constant vector is `-1`.

The theorem allows arbitrary input dimension and arbitrary Kraus
rank. Its target has at most two full matrix blocks, selected by
the repaired involution; it does not assume a Schur form for the
original channel. It strengthens a qualitative reflection argument
by deriving near multiplicativity from the CP and mixed-norm
near-involutivity hypotheses themselves.

The native long-time Kazhdan heat estimates do not supply this CP
lower bound by half the identity map. A heat Poisson expansion has
an explicit identity term whose coefficient decreases to zero as
time grows; that observation alone neither establishes nor rules out
the stronger CP lower bound. General heat rounding and the native
nonhyperlinearity problem remain outside this result.
