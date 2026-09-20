# Acceptance of four analytic leaves in Liu Sections 3–5

Date: 2026-09-20.

## Attribution, scope, and meaning of acceptance

The results and mechanisms below are due to **Jihao Liu**, [*Nonhyperlinear
groups exist*, September 20, 2026](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf),
Theorems 3.2 and 4.3 and Lemmas 5.2–5.4, printed pages 8–23. This is an
independent verification and expanded exposition of Liu's proofs, not a
claim of new results, new mechanisms, or priority for Cairn. It supplements
the earlier partial [block-construction audit](liu-block-construction-audit-2026-09-20.md).

This acceptance is limited to the four exact canonical interfaces named
below. Their proofs have been reconstructed, including their quantifiers,
normalizations, variable-outcome bounds, and limiting arguments. None is
accepted merely because an earlier reading found no gap. The proofs are
ordinary written mathematical proofs, not Lean certificates. They use
standard spectral calculus, polar decomposition, tracial ultraproducts,
and the two explicitly credited finite von Neumann algebra lemmas in
Section B. They do not assert a verification of the whole paper, Theorem
5.1's assembly, Sections 6–8, or the final nonhyperlinearity conclusion.

| Exact canonical claim | Liu result | Acceptance basis |
| --- | --- | --- |
| `quotient-gap-gives-uniform-relative-projection-repair` | Theorem 3.2 | Complete reconstruction in A |
| `low-energy-povms-round-equivariantly-in-place` | Theorem 4.3 | Complete reconstruction in B, with two identified standard imports |
| `resolvent-assembly-controls-covariance-and-leakage` | Lemmas 5.2, 5.3 | Complete reconstruction in C |
| `defective-block-expansion-prunes-to-doubled-gaps` | Lemma 5.4 | Complete reconstruction in D |

No local mathematical obligation in these four interfaces remains open
in this written proof. That statement is bounded by the stated imports
and scope; it is not an assertion that computer compilation checks these
analytic arguments. In particular, accepting these leaves does not by
itself accept any route assembling them into later theorems.

## Conventions

Write `tau=Tr/d`, and give *every rectangular Hilbert–Schmidt norm* the
same denominator `d`, even on an auxiliary space. For a fixed list of
`h>=1` unitaries, set

```text
E(x) = (1/(4h)) sum_j ||[u_j,x]||_2^2,
T(x) = x/2 + (1/(4h)) sum_j (u_j x u_j* + u_j* x u_j),
D = I-T.
```

As operators on Hilbert–Schmidt space, `0<=T<=I`, `0<=D<=I`, and
`E(x)=<Dx,x>`. Here an `I` acting on matrices and the identity matrix
will be distinguished by context. A scalar gap for a list of `k`
unitaries is `sum ||[u_j,x]||_2^2/(4k)>=c||x||_2^2` on trace-zero
matrices, using the normalized trace of the block in question.

For A only, fix a nonprincipal ultrafilter `omega`, dimensions `d_n`,
and the coordinate unitaries. In the tracial algebra ultraproduct `M`,
put `C={u_1,...,u_h}' cap M`. Assume the induced `T` has spectral gap
`a in (0,1)` on `L2(M) minus L2(C)`. This is a gap on the trace Hilbert
space of the **algebra ultraproduct**, not on the full Hilbert
ultraproduct of coordinate Hilbert–Schmidt spaces. Fixed vectors of `T`
are `L2(C)`: the Dirichlet-form identity identifies bounded fixed
vectors, and mean ergodic averaging on bounded elements, followed by
density, gives the full Hilbert-space identification.

## A. All-rank relative projection repair — Liu Theorem 3.2

### A.1 Exact output and additive transfer

Let `L=36/a^2`. We prove there exist `e_n` and `eta_n>0`, chosen before
any test projection, with `tau(1-e_n)->_omega 0`, `eta_n->_omega 0`,
such that every coordinate projection `p<=e_n` satisfying
`E_n(p)<=tau(p)/(4L)` has a projection `f` in that same matrix algebra
with

```text
||f-p||_2^2 <= L E_n(p),
tau(p)/4 <= tau(f) <= 9 tau(p)/4,
E_n(f) <= eta_n tau(f).
```

There is no positive lower bound on `tau(p)`, and no conclusion `f<=e_n`.
Put `r=1-a`. Spectral calculus on the quotient gives
`||T^k D x||_2<=r^k||Dx||_2` because `Dx` is orthogonal to `L2(C)`.
For fixed `k>=1`, define

```text
delta_(k,n) = max(0, sup_{p projection}
                    (||T_n^k D_n p||_2-r^k||D_n p||_2)).
```

Then `delta_(k,n)->_omega 0`. Otherwise choose violating projections
coordinatewise on an omega-large set; they are uniformly operator-norm
bounded, and their class contradicts the quotient inequality. This is
a uniform **additive** estimate on all coordinate projections. It does
not yet justify relative estimates on low-rank inputs.

### A.2 Removing one exceptional corner before all tests

Fix `eta in (0,1]`. Choose `K>=1` and `zeta>0`, independent of `n`, so

```text
r^K <= eta^2/1152,
zeta <= min(1/K, eta^2/1152).
```

For `1<=k<=K`, call a coordinate projection `q` bad if

```text
||T_n^k D_n q||_2 >= (r^k+zeta)||D_n q||_2,
||D_n q||_2 >= eta ||q||_2.
```

Zero is bad. Choose a bad projection `q_(k,n)` of maximal rank. This
only uses the finite set of possible ranks, not attainment of an
optimization over an open set. The additive estimate implies

```text
eta zeta sqrt(tau(q_(k,n))) <= delta_(k,n).
```

Let `B_(k,n)` project onto the span of `w ran(q_(k,n))` for words of
length at most `2k+2` in `I,u_1,u_1*,...,u_h,u_h*`. Padding with `I`
shows

```text
tau(B_(k,n)) <= (2h+1)^(2k+2) delta_(k,n)^2/(eta^2 zeta^2).
```

No nonzero `p<=1-B_(k,n)` is bad. Indeed, the word spans of lengths
at most `k+1` of `p` and `q_(k,n)` are orthogonal: inner products
reduce to words of length at most `2k+2` applied to `q_(k,n)`.
Both `D_n(v)` and `T_n^k D_n(v)` have their ranges and adjoint ranges
in that word span of `v`. Consequently their squared norms add for
`v=p+q_(k,n)`. If `p` were bad, addition of both squared defining
inequalities would make `p+q_(k,n)` bad of larger rank, a contradiction.

Set `e_(n,eta)=1-join_(k<=K) B_(k,n)`. Its complement trace tends to
zero. Every nonzero `p<=e_(n,eta)` has either

```text
||D_n p||_2 < eta ||p||_2,
```

or, simultaneously for every `1<=k<=K`,

```text
||T_n^k D_n p||_2 <= (r^k+zeta)||D_n p||_2.
```

The construction precedes `p`; thus this is the required all-rank
uniformity, not a diagonal argument on a previously selected sequence
of input projections.

### A.3 Averaging and a cut, with relative constants

For `p=0` take `f=0`. In the first alternative take `f=p`, since
`E(p)=<Dp,p><eta tau(p)`. In the second put `z=T_n^K(p)` and
`theta=r^K+zeta<=eta^2/576`. Then `0<=z<=I`, `tau(z)=tau(p)`, and

```text
||Dp||_2^2 <= E(p),
||z-p||_2 <= (sum_(j=0)^(K-1) r^j + (K-1)zeta)||Dp||_2
           <= (2/a)||Dp||_2,
||Dz||_2 <= theta sqrt(tau(p)),
E(z) <= theta tau(p).
```

In an eigenbasis of `z`, with eigenvalues `lambda_i`, the energy is
`sum_(i,l) w_(i,l)(lambda_i-lambda_l)^2`, where
`w_(i,l)=sum_j |(u_j)_(i,l)|^2/(4hd)`. Each row and column has total
weight `1/(4d)`. The total weight incident to eigenvalues at least
`1/3` is at most `3 tau(z)/2`. For `f_t=1_[t,1](z)`, integration over
`t in [1/3,2/3]` and weighted Cauchy–Schwarz therefore give

```text
integral E(f_t) dt <= sqrt(3 tau(z) E(z)/2).
```

Some cut in this interval has `E(f_t)<=6 sqrt(tau(z)E(z))`. This uses
only the interval length `1/3`; the constant is deliberately slack.
For any such `t`, write `beta_i=<p xi_i,xi_i>` in that eigenbasis.
The contribution to `d||z-p||_2^2` is

```text
lambda_i^2(1-beta_i)+(1-lambda_i)^2 beta_i.
```

The contribution to `d||f_t-p||_2^2` is `beta_i` below the cut and
`1-beta_i` above it. In the two respective cases `1-lambda_i>=1/3`
and `lambda_i>=1/3`. Hence

```text
||f_t-p||_2^2 <= 9||z-p||_2^2 <= (36/a^2) E(p).
```

This calculation does not assume `p` commutes with `z`. The input
energy bound makes `||f_t-p||_2<=||p||_2/2`; the norm triangle and
reverse triangle give the two required trace bounds. Finally

```text
E(f_t) <= 6 sqrt(theta) tau(p)
       <= eta tau(p)/4 <= eta tau(f_t).
```

### A.4 One diagonal choice for every coordinate

Apply the preceding construction to each fixed `eta=1/m`. Let

```text
Lambda_m = intersection_(i=1)^m
             {n: tau(1-e_(n,1/i))<=1/m}.
```

These are decreasing omega-large sets. For `n in Lambda_1`, let
`m(n)=max{m<=n:n in Lambda_m}` and set
`e_n=e_(n,1/m(n))`, `eta_n=1/m(n)`. Else set `e_n=0,eta_n=1`.
For each fixed `J`, `Lambda_J intersection {n>=J}` is omega-large,
so `m(n)->_omega infinity`; also `tau(1-e_n)<=1/m(n)` on
`Lambda_1`. The fixed-target proof applies to every input in the
chosen corner at that coordinate. On the other coordinates only
`p=0` is eligible. This proves the exact all-coordinate theorem.

## B. In-place equivariant POVM rounding — Liu Theorem 4.3

### B.1 Exact target and the two finite-algebra imports

For every fixed `h>=1` and `epsilon>0`, there is
`delta=delta(h,epsilon)>0`, independent of `d` and outcome count `m`,
such that `a_i>=0`, `sum_i a_i=I`, and `sum_i E(a_i)<=delta` imply
a PVM `q_i` in the same `M_d` satisfying

```text
sum_i E(q_i) <= epsilon,
sum_i ||q_i-a_i||_2^2 <= 5000 sum_i tau(a_i-a_i^2)+epsilon.
```

The proof uses the following published finite-von-Neumann-algebra
facts, with attribution retained from Liu's Lemmas 4.1 and 4.2:

1. Cyril Houdayer and Stefaan Vaes, *Type III factors with unique
   Cartan decomposition*, [Lemma 2.1](https://arxiv.org/pdf/1203.1254):
   in a von Neumann algebra with a faithful normal semifinite trace,
   if that trace restricts semifinitely to a MASA, every finite-trace
   projection is equivalent to a projection in the MASA. We use this
   only in a finite algebra, so the trace restriction condition is
   automatic.
2. Adrian Ioana, *Almost commuting matrices and stability for product
   groups*, [Lemma 2.2(1)](https://ems.press/content/serial-article-files/47873):
   equivalent projections `p,q` in a finite tracial algebra admit a
   unitary `U` with `UpU*=q` and `||U-1||_2<=3||p-q||_2`.
   Rescaling the trace rescales both sides equally.

The hypotheses of these primary-source statements have been checked
at the point of use below. Their background proofs are standard
imports, not claimed as newly proved here. Neither statement assumes
matrix-coordinate internality of the algebra in which it is applied.

### B.2 Cuts with energy and overlap bounds

For a positive contraction `b`, coarea on `[1/3,2/3]` gives a cut
`f=1_[t,1](b)` with `E(f)<=4 sqrt(tau(b)E(b))`. Indeed the integral
of each squared commutator is bounded by the weighted sum of
`|lambda_r-lambda_s|` over pairs incident to an eigenvalue at least
`1/3`; the second Cauchy–Schwarz factor is at most
`sqrt(6 tau(b))` before the energy normalization. Summing over
`h` generators and averaging over the interval gives the constant
`3sqrt(6)/2<4`.

Apply this to every `a_i`. Put `beta=sum_i E(a_i)`,
`v_d=sum_i tau(a_i-a_i^2)`, and `S=sum_i f_i`. Scalar calculus gives

```text
f_i <= 3 a_i,
|f_i-a_i| <= 3 a_i(1-a_i),
|f_i-a_i|^2 <= 2 a_i(1-a_i).
```

Thus, without a factor `m`,

```text
sum_i E(f_i) <= 4 sqrt(beta),
0<=S<=3I,   |tau(S)-1|<=3v_d,
sum_i ||f_i-a_i||_2^2<=2v_d.
```

Also `sum_(k!=i) f_k<=3(I-a_i)`. Taking its trace against `f_i`
and using `f_i<=3a_i` gives
`sum_(i!=k) tau(f_i f_k)<=9v_d`. Hence
`||S-I||_2^2<=12v_d`.

### B.3 An invariant auxiliary partial isometry

Consider any sequence of such data with `sum_i E_n(a_i)->_omega 0`
and fixed `h`. Let `v=lim_omega v_(d_n) in [0,1]`. Form

```text
H_n = C^(d_n),
K_n = H_n direct-sum direct-sum_i f_(i,n)H_n.
```

Let `E_n` project onto the physical summand, `F_(i,n)` onto the
individual auxiliary summands, and `F_n=sum_i F_(i,n)`. Then
`d_n<=dim K_n<=4d_n`. Use `sigma_n=Tr_(K_n)/d_n`, not normalization
by the auxiliary dimension. Define the column `W_n xi=(f_(i,n)xi)_i`.
It satisfies `W_n*W_n=S_n` and `||W_n||<=sqrt(3)`.

Complete the polar part of each square compression `f_i u_j f_i`
to a unitary `w_(j,i)` on `f_iH`. The inequality
`(1-s)^2<=1-s^2` for its singular values, and orthogonal source
corners, give

```text
||w_(j,i) f_i-f_i u_j||_2^2 <= ||[u_j,f_i]||_2^2.
```

Consequently `uhat_(j,n)=u_(j,n) direct-sum direct-sum_i w_(j,i,n)`
commutes with every label projection and
`||uhat_j W_n-W_n u_j||_2^2<=sum_i||[u_j,f_i]||_2^2->_omega 0`.

In the tracial ultraproduct `N` of `B(K_n)`, the trace `sigma` induced
by `sigma_n` is a faithful normal finite trace: it is a positive
scalar multiple of the usual normalized ultraproduct trace since
`1<=dim K_n/d_n<=4`. Put `D={uhat_1,...,uhat_h}' cap N`. Then
`E,F,W` lie in `D`, `sigma(E)=1`, and `W=FWE`.

Retain the entire internal scalar-label algebra

```text
L_n={sum_i alpha_i F_(i,n): alpha_i complex},
L=[L_n]_omega subset FDF.
```

This includes arbitrary coordinate-dependent bounded choices of
labels/phases, not just fixed label sequences. Its unit ball is closed
in 2-norm because coordinate conditional expectations induce a
contractive idempotent with precisely that range; hence it is a von
Neumann algebra. Choose a MASA `A` of `FDF` containing `L`.

Take the polar decomposition `W=V|W|` inside `D`, with `e=V*V<=E`,
`f=VV*<=F`. The bound on `||S-I||_2^2`, functional calculus using
`(sqrt(s)-1)^2<=(s-1)^2`, and the kernel of `S` imply

```text
sigma(E-e)<=12v,
||V-W||_2^2<=12v,
sigma(F-f)<=15v.
```

If `F!=0`, the Houdayer–Vaes lemma applies in the **finite** algebra
`FDF` with MASA `A`. Choose `p_0 in A` equivalent to `F-f`, and
put `ftilde=F-p_0`. Then

```text
||f-ftilde||_2^2 <= sigma(F-f)+sigma(p_0)<=30v.
```

Ioana's lemma applies to the equivalent `p_0,F-f` in this same
algebra, with identity `F`. It gives `U p_0 U*=F-f` and
`||U-F||_2<=3sqrt(30v)`. Thus `U ftilde U*=f`, without any separate
assumption about equivalence of complements. Set `Z=U*V`. Then

```text
Z in D,   Z*Z=e,   ZZ*=ftilde,   [ftilde,L]=0,
||Z-W||_2 <= (sqrt(270)+sqrt(12))sqrt(v) <=20sqrt(v).
```

If `F=0`, take `ftilde=Z=0`; all identities and estimates persist.
This operation uses abstract finite-algebra comparison only. It does
not assume that `D` or `A` is internal, nor attempt to lift a MASA.

### B.4 Lift one label-diagonal range and return to physical dimension

Choose positive contraction representatives `y_n` of `ftilde` in
`F_n B(K_n) F_n`, and pinch by labels:
`P_n(y)=sum_i F_(i,n)yF_(i,n)`. Direct off-diagonal block expansion
gives the exact identity

```text
2||y-P_n(y)||_2^2
  = integral_(phases zeta_i) ||[y,sum_i zeta_i F_(i,n)]||_2^2.
```

If the pinching error did not tend to zero, choose witnessing phases
at each coordinate of an omega-large set. Their bounded sequence is
an element of `L`, contradicting `[ftilde,L]=0`. Hence `P_n(y_n)`
still represents `ftilde`. Cutting at `1/2` produces projections
`ftilde_n` representing it and commuting with all labels, since
`|1_[1/2,1](s)-s|<=2|s-s^2|` on `[0,1]`.

As `sigma(ftilde)=sigma(e)<=1`, the excess
`(rank(ftilde_n)-d_n)_+/d_n` tends to zero. Delete exactly this
excess within the individual label blocks to get projections `g_n`
of rank at most `d_n`, still representing `ftilde` and commuting
with every label. This is possible regardless of the number or ranks
of labels.

Choose contraction lifts `z_n` of `Z` in `F_n B(K_n) E_n` and put
`z'_n=g_n z_n`. Then `g_n-z'_n z'_n*` is positive and tends to zero
in 2-norm. Extend the polar part of `z'_n` to a partial isometry
`t_n:H_n onto g_n K_n`. The rank inequality gives enough domain
dimension. Including zero left singular values,

```text
||t_n-z'_n||_2^2 <= sigma_n(g_n-z'_n z'_n*) ->_omega 0.
```

The trace limit follows by Cauchy–Schwarz and `sigma_n(I)<=4`.
Thus `[t_n]=Z`, `t_n t_n*=g_n`, and `e'_n=t_n*t_n` represents `e`.
Define

```text
g_(i,n)=F_(i,n)g_n,
Q_(i,n)=t_n* g_(i,n) t_n,
q_(1,n)=Q_(1,n)+E_n-e'_n,
q_(i,n)=Q_(i,n)  (i>=2).
```

The `Q_i` are orthogonal projections with sum `e'_n`. Therefore
the `q_i` form a PVM with exactly the original labels in `M_(d_n)`.

### B.5 Summed energy, distance, and the uniform quantifier

Fix `j` and write `rho=uhat_j t-t u_j`. Since `Z in D`, its norm
tends to zero. The inverse-unitary defect
`rho_-=uhat_j* t-t u_j*=-uhat_j* rho u_j*` has the same norm.
Because labels commute exactly with `uhat_j`, their disjoint supports
give

```text
sum_i ||[uhat_j,g_i]||_2^2 = ||[uhat_j,g]||_2^2 ->_omega 0.
```

Expand

```text
[u_j,Q_i] = -rho_-* g_i t + t*[uhat_j,g_i]t + t*g_i rho.
```

The direct-sum squared norm of the first terms is at most
`||rho||_2^2`; the same is true for the third terms. The middle
terms are bounded by the preceding summed identity. Consequently

```text
sum_i ||[u_j,Q_i]||_2^2
 <= 3(2||rho||_2^2+||[uhat_j,g]||_2^2).
```

Also `||[u_j,E-e']||_2<=2||rho||_2`. Completing the first outcome
and using squared triangle inequalities gives

```text
sum_i ||[u_j,q_i]||_2^2
 <=20||rho||_2^2+6||[uhat_j,g]||_2^2 ->_omega 0.
```

The number `h` is fixed, so `sum_i E_n(q_i)->_omega 0`.
The possibly nonvanishing trace of `E-e'` is harmless: its
commutator vanishes, which is the required output condition.

For distance let `t_i=F_i t`, `W_i=F_i W`. Both are contractions,
and their Gram matrices are `Q_i` and `f_i`. Expanding the Gram
difference yields

```text
sum_i ||Q_i-f_i||_2^2 <=4sum_i ||t_i-W_i||_2^2
                       =4||t-W||_2^2.
```

The ultralimit is at most `1600v`. The squared norm of the completing
remainder has limit at most `12v`; the cut distance has limit at
most `2v`. The Hilbert direct-sum triangle inequality therefore gives

```text
lim_omega sum_i ||q_i-a_i||_2^2
 <=(40+sqrt(12)+sqrt(2))^2 v <=5000v.
```

This includes `v=0`; no division by `v` occurred. If the stated
finite theorem failed for fixed `h,epsilon`, choose a counterexample
with input energy at most `1/n` for each `n`, allowing arbitrary
`d_n,m_n`. The construction just proved gives output energy tending
to zero and the ultralimit of
`sum_i||q_i-a_i||_2^2-5000v_(d_n)` at most zero. Both required
inequalities then hold on an omega-large set, a contradiction.
Thus `delta` is independent of both dimension and label count.

## C. Monotone resolvents — Liu Lemmas 5.2 and 5.3

### C.1 Rectangular resolvent and inclusion defect

Given any finite family of projections `f_i` in `M_d` and `mu>0`, put

```text
S_i=sum_(k<=i) f_k,   D_i=(I+mu S_i)^(-1),
B_i=D_(i-1)-D_i.
```

The empty family gives only `D_0=I` and is immediate. Zero projections
may be omitted. Let `K_i=f_i H`, let `F_i:H->K_i` be the row `f_i`,
and `F` their column. For each unitary `u`, complete the polar part
of `f_i u f_i` to `v_i` on `K_i`, and put `V=direct-sum_i v_i`.
The same two-corner singular-value calculation as B.3 gives

```text
delta_u^2 := ||VF-Fu||_2^2 <=sum_i||[u,f_i]||_2^2.
```

The inclusion defect for `V*,u*` has exactly the same norm.
For `Q_mu(Z)=(I+mu Z*Z)^(-1)`, differentiation gives

```text
dot Q = -mu Q(dot Z* Z+Z* dot Z)Q.
```

Singular values give `||Q||<=1` and `||ZQ||<=1/(2sqrt(mu))`, so
`||dot Q||_2<=sqrt(mu)||dot Z||_2`. Integrate along a line.
The equivariance `Q_mu(VFu*)=u Q_mu(F)u*` then gives

```text
||[u,D_l]||_2^2<=mu sum_(i<=l)||[u,f_i]||_2^2
```

for each prefix. Averaging over the generators proves (5.1).

### C.2 Block Cholesky, with no label-count constant

Factor `I_K+mu ZZ*=C(Z)C(Z)*`, with `C` lower block triangular and
positive definite diagonal blocks. Successive positive Schur
complements give existence, uniqueness, and differentiability.
Put `J=C^(-1)Z`. Along a differentiable path set

```text
Xi=C^(-1) dot C,
Upsilon=C^(-1) mu(dot Z Z*+Z dot Z*) C^(-*).
```

Then `Xi+Xi*=Upsilon`. Strict lower blocks of `Xi` equal those of
`Upsilon`; upper blocks vanish. On a diagonal block, write
`C_ii=G>0` and `dot C_ii=H=H*`. Then
`Xi_ii=G^(-1)H`, `Upsilon_ii=G^(-1)H+HG^(-1)`. In an eigenbasis of
`G`,

```text
(Xi_ii)_(r,s)=g_s/(g_r+g_s) (Upsilon_ii)_(r,s).
```

Summing squared entries over all blocks gives
`||Xi||_2<=||Upsilon||_2`, independently of their number and sizes.
Moreover `||C^(-1)||<=1` and

```text
mu JJ* = I-C^(-1)C^(-*) <= I.
```

Hence `||Upsilon||_2<=2sqrt(mu)||dot Z||_2` and
`dot J=C^(-1)dot Z-Xi J` gives `||dot J||_2<=3||dot Z||_2`.
Thus `J` is 3-Lipschitz. Uniqueness of positive diagonal factors
gives `C(VZu*)=VC(Z)V*` and `J(VZu*)=VJ(Z)u*` for block-diagonal
`V`.

At `Z=F`, set `W=sqrt(mu)J(F)`, and
`H_i=F_i D_(i-1) F_i*`, a positive contraction. Block elimination
using

```text
I-mu F_<i* (I+mu F_<i F_<i*)^(-1) F_<i = D_(i-1)
```

gives

```text
C_ii=(I+mu H_i)^(1/2),
W_i=sqrt(mu)(I+mu H_i)^(-1/2) F_i D_(i-1).
```

Multiplication verifies the Woodbury identity

```text
B_i=mu D_(i-1) F_i* (I+mu H_i)^(-1) F_i D_(i-1)=W_i*W_i.
```

Thus `B_i>=0`, `rank B_i<=rank f_i`, and telescoping gives
`W*W=I-D_m<=I`. Lipschitz continuity and equivariance yield

```text
sum_i||v_i W_i-W_i u||_2^2<=9mu delta_u^2,
```

and the identical inverse-unitary bound. Expanding
`[u,W_i*W_i]=(uW_i*-W_i*v_i)W_i+W_i*(v_iW_i-W_i u)` and using
the contraction bounds proves
`sum_i||[u,B_i]||_2^2<=36mu delta_u^2`. Expanding for the single
entire contraction `W` proves `||[u,D_m]||_2^2<=36mu delta_u^2`.
Averaging these two inequalities proves (5.2) with `72mu`.

### C.3 Recover the localized covariance estimate

The row formula implies

```text
W_i F_i*=g_mu(H_i),   g_mu(x)=sqrt(mu) x/sqrt(1+mu x).
```

Expand its commutator with `v_i`, using the intertwining defects of
`W_i` and `F_i`. Their direct-sum squared norms give

```text
sum_i ||[v_i,g_mu(H_i)]||_2^2 <=2(9mu+1)delta_u^2.
```

On `[0,1]`, `g_mu'(x)>=ell_mu=sqrt(mu)/(1+mu)^(3/2)>0`.
Entrywise divided differences in an eigenbasis of `H_i` therefore
give

```text
sum_i ||[v_i,H_i]||_2^2
 <=2(9mu+1)ell_mu^(-2)delta_u^2.
```

The square-root function `x -> sqrt(1+mu x)` is `mu/2`-Lipschitz
on this interval. Another entrywise calculation gives

```text
sum_i||[v_i,C_ii]||_2^2 <= M_mu delta_u^2,
M_mu=mu^2(9mu+1)/(2ell_mu^2).
```

Taking adjoints in the row formula gives
`D_(i-1)F_i*=mu^(-1/2)W_i*C_ii`. Thus

```text
u D_(i-1)F_i*-D_(i-1)F_i*v_i
 =mu^(-1/2)((uW_i*-W_i*v_i)C_ii+W_i*[v_i,C_ii]).
```

Its direct-sum squared norm is at most
`2mu^(-1)(9mu(1+mu)+M_mu)delta_u^2`. Subtract
`D_(i-1)(uF_i*-F_i*v_i)` and use squared triangle inequalities to
obtain

```text
sum_i||[u,D_(i-1)]f_i||_2^2 <= C_mu sum_i||[u,f_i]||_2^2,
C_mu=36(1+mu)+4M_mu/mu+2.
```

The restriction to `K_i` has the same Hilbert–Schmidt norm as right
multiplication by `f_i`, which identifies the displayed expression
with the one just estimated. All parameters depend only on `mu`.

### C.4 Fixed continuous functions and the order of limits

The linear span of `1` and the resolvents `(x+s)^(-1)`, `s>0`, is
uniformly dense in `C([0,infinity])`. To verify this without assuming
that the span is an algebra, use `y=(1+x)^(-1)`. Polynomial
approximation on `[0,1]` handles continuous functions of `y`, and

```text
(partial/partial s)^(r-1) (x+s)^(-1) at s=1
  =(-1)^(r-1)(r-1)! (1+x)^(-r).
```

Finite differences approximate each derivative uniformly for `x>=0`
because the next derivative is uniformly bounded for `s` near 1.
The same argument gives density on `[0,1]`, after extending the
corresponding continuous function of `y` to all of `[0,1]`.

Each resolvent is a scalar multiple of a `D^(mu)` already covered
by C.3. For a fixed approximant to `psi` with uniform error `rho`,

```text
sum_i||[u,(psi-r)(S_(i-1))] f_i||_2^2
 <=4rho^2 sum_i tau(f_i).
```

If the rightmost total trace is uniformly bounded and the input
total energies tend to zero, first fix the approximant, take the
ultrafilter limit for its finitely many terms, then let `rho` tend
to zero. This proves (5.4), with no simultaneous approximation
depending on the coordinate and no factor counting outcomes.

### C.5 Range leakage for any positive monotone chain

Now let `I=D_0>=D_1>=...>=D_m>=0` be *any* chain and
`B_i=D_(i-1)-D_i`. For `s>0`, put `A=D_(i-1)+sI`. The exact
noncommutative inverse identity

```text
(A-B_i)^(-1)-A^(-1)-A^(-1)B_i A^(-1)
 = A^(-1)B_i(A-B_i)^(-1)B_i A^(-1) >=0
```

can be checked by two resolvent identities. Summing telescopes and
gives

```text
sum_i (D_(i-1)+sI)^(-1) B_i (D_(i-1)+sI)^(-1) <= s^(-1)I.
```

The constant function has bound `sum_i B_i<=I`. For
`r(x)=c_0+sum_k c_k/(x+s_k)`, apply the triangle inequality in
the direct sum of vectors `B_i^(1/2) r(D_(i-1))* xi` to obtain

```text
sum_i r(D_(i-1)) B_i r(D_(i-1))* <= K_r I,
K_r=(|c_0|+sum_k |c_k|/sqrt(s_k))^2.
```

For fixed continuous `g` choose such `r` with `||g-r||_infinity<=rho`.
Since `sum_i tau(B_i)<=1`,

```text
sum_i||(g-r)(D_(i-1)) B_i^(1/2)||_2^2<=rho^2.
```

Left-multiply the amplitudes by `I-e` and use the squared triangle
inequality. For every projection `e`,

```text
sum_i tau((I-e)g(D_(i-1)) B_i g(D_(i-1))*)
 <=2K_r tau(I-e)+2rho^2.
```

This is the claimed dimension- and label-independent bound. If
`tau(I-e_n)->_omega 0`, keep `r` fixed during the limit and then
let `rho` decrease to zero. The positive trace pairing preserves
order, so the same vanishing conclusion holds for positive matrices
dominated by a fixed multiple of these summands. No commutation
between different `D_i` has been assumed.

## D. Prune defects and double generators — Liu Lemma 5.4

### D.1 Exact hypotheses and pruning one block

Let `P_0,...,P_m` be a PVM, and suppose each `w_j` reduces every
`P_i`. Assume `0<theta<=1`, `xi_i>=0` for `i>=1`, and every
`q<=P_i` of rank at most `rank(P_i)/2` satisfies

```text
E_w(q)>=theta tau(q)-xi_i.
```

Write `xi=sum_(i>=1)xi_i`. Fix nonzero `P=P_i`. If
`xi_i>theta tau(P)/8`, discard it (`R_i=0`), losing less than
`8xi_i/theta` trace. Otherwise put `kappa=theta/8` and start
`Q=P`. Whenever a nonzero `p<=Q` satisfies

```text
tau(p)<=tau(Q)/2,
E_(w,Q)(p):=sum_j||[Qw_jQ,p]||_2^2/(4h)<kappa tau(p),
```

remove `p` from `Q`. Rank strictly decreases, no removal exhausts
`Q`, and the process terminates at a nonzero `R`.

For any initial segment `p_1,...,p_l`, let `A=sum p_k` and let
`Q_k` be the remainder just before the `k`th removal. The entries
joining `A` to `P-A` are, for each `p_k`, a subset of the entries
joining `p_k` to `Q_k-p_k`; these different endpoints give
orthogonal Hilbert–Schmidt contributions. As `P` reduces the
original unitaries,

```text
E_w(A)=E_w(P-A)<=sum_k E_(w,Q_k)(p_k)<=kappa tau(A).
```

No initial segment can first reach `tau(A)>=tau(P)/4`: at a first
crossing its preceding trace is less than `tau(P)/4`, and the
half-size rule gives `tau(A)<5tau(P)/8`. The smaller of `A,P-A`
has trace between `tau(P)/4` and `tau(P)/2`, so the original
expansion hypothesis gives

```text
E_w(A)>=theta tau(P)/4-xi_i>=theta tau(P)/8.
```

The boundary estimate gives instead
`E_w(A)<5theta tau(P)/64`, a contradiction. At termination the
removed `A=P-R` therefore has trace below `tau(P)/4`. Applying
the original hypothesis to it and combining the two inequalities
gives

```text
tau(P-R)<=8xi_i/(7theta),
E_w(R)<=xi_i/7.
```

Termination also gives, for every half-size `p<=R`,
`E_(w,R)(p)>=kappa tau(p)`. Set `R_i=0` if `P_i=0`; combine all
retained and discarded blocks. The sums satisfy

```text
tau(R_0)-tau(P_0)<=8xi/theta,
sum_(i>=1)E_w(R_i)<=xi/7,
R_0=I-sum_(i>=1)R_i.
```

This charges each original additive defect just once. There is no
minimum allowed block trace.

### D.2 From projection expansion to all complex trace-zero matrices

On a retained block of rank `r`, use `tau_r=Tr/r`, put
`a_j=Rw_jR`, and define

```text
Q(x)=sum_j (||[a_j,x]||_(2,r)^2+||[a_j*,x]||_(2,r)^2)/(8h).
```

The `a_j` are contractions. For selfadjoint inputs the paired
commutator norms agree. Dividing the terminal projection estimate
by `tau_d(R)` gives `Q(p)>=kappa tau_r(p)` for all half-size
projections in this block.

If `y>=0` has support trace at most `1/2`, its projections
`p_s=1_(s,infinity)(y^2)` satisfy the same condition. In an eigenbasis
of `y`, layer-cake and Cauchy–Schwarz yield

```text
kappa tau_r(y^2) <= integral_0^infinity Q(p_s) ds
 =sum_(j,b,k) |y_b^2-y_k^2| |(a_j)_(b,k)|^2/(4hr)
 <=sqrt(Q(y)) sqrt(H(y)),
H(y)=sum_(j,b,k) (y_b+y_k)^2 |(a_j)_(b,k)|^2/(4hr).
```

Every row and column of a contraction has squared Euclidean norm
at most one. Using `(s+t)^2<=2(s^2+t^2)` gives
`H(y)<=tau_r(y^2)`. Thus `Q(y)>=kappa^2 tau_r(y^2)` (the zero
case is immediate).

For selfadjoint `x` choose a median eigenvalue `b`. Both
`y_+=(x-bI)_+` and `y_-=(bI-x)_+` have support trace at most
one half, including odd rank and repeated median eigenvalues.
Entrywise the scalar inequality

```text
|s-t|^2 >= |(s-b)_+-(t-b)_+|^2
           + |(b-s)_+-(b-t)_+|^2
```

gives `Q(x)>=Q(y_+)+Q(y_-)`. If `tau_r(x)=0`, it follows that

```text
Q(x)>=kappa^2 tau_r((x-bI)^2)>=kappa^2||x||_(2,r)^2.
```

For completeness the Hilbert–Schmidt operator defining `Q` is

```text
L(x)=sum_j ((a_j*a_j+a_j a_j*)x+x(a_j*a_j+a_j a_j*)
             -2a_j*x a_j-2a_j x a_j*)/(8h).
```

It is selfadjoint and preserves adjoints. For selfadjoint `A,B`,
`tau_r(A L(B))` is real, so `Q(A+iB)=Q(A)+Q(B)`. The real and
imaginary parts of a complex trace-zero matrix are themselves
trace zero, and their squared norms add. The same gap therefore
holds for **all complex** trace-zero matrices, not just selfadjoint
ones.

### D.3 Two nearby unitary copies and the exact total cost

On each final block `R` (including `R_0`), extend the polar part
of `a=Rw_jR` to a unitary `v` and put

```text
z_(j,R)^+/-=v(|a| +/- i sqrt(R-|a|^2)).
```

These are unitaries with average `a`. Their block sums give
`z_j^+,z_j^-` reducing every `R_i`. Convexity applied to both
`a` and `a*`, and the identity
`[z*,x]=-z*[z,x]z*` for a unitary, show

```text
sum_(j,+/-)||[z_(j,R)^+/-,x]||_(2,r)^2/(8h)>=Q(x).
```

The denominator is the scalar-gap normalization for the **doubled**
list of `2h` unitaries. Hence its gap is
`kappa^2=theta^2/64` on every nonzero retained block.

Set `C_j=sum_R Rw_jR` and `L_j=||w_j-C_j||_2^2`. Diagonal and
off-diagonal blocks are orthogonal, and the singular-value formula
for the constructed copies gives

```text
||z_j^+/- - C_j||_2^2
 =sum_R tau(R-(Rw_jR)*(Rw_jR))=L_j,
||z_j^+/- - w_j||_2^2=2L_j.
```

Writing `B=sum_R E_w(R)`, direct block expansion gives
`B=sum_j L_j/(2h)`. Since each original `P_i` reduces each `w_j`,
the only new boundary within `P_i` joins `R_i` to `P_i-R_i`.
Therefore

```text
E_w(R_0)=sum_(i>=1)E_w(R_i),
B=2sum_(i>=1)E_w(R_i)<=2xi/7.
```

Summing the edits over both signs yields
`sum_(j,+/-)||z_j^+/- - w_j||_2^2=8hB<=16hxi/7`.
This proves all three conclusions of the canonical pruning claim.

## E. Dependency and acceptance boundary

The written proofs above have the following dependency structure:

```text
quotient spectral gap
  -> bounded projection witnesses
  -> maximal bad-projection word-neighborhood exclusion
  -> relative averaging and coarea cut
  -> uniform relative repair (A)

coarea cuts + finite-algebra projection comparison/conjugacy
  -> invariant auxiliary partial isometry
  -> all-label pinching + rank-corrected physical lift
  -> in-place equivariant PVM (B)

rectangular resolvent + positive-diagonal block Cholesky
  -> summed and localized covariance
monotone inverse identity + resolvent approximation
  -> summed range leakage (C)

defective half-rank expansion
  -> pruning + compressed Cheeger inequality
  -> doubled unitary realization with cost (D)
```

None of A–D assumes large scalar-expanding decompositions, Kazhdan
commutant internality, all-trace normalization, or nonhyperlinearity.
In B the auxiliary commutant is used only as an abstract finite
algebra. Consequently these leaves do not introduce the suspected
internality cycle. All parameters used in limit/approximation
arguments are fixed before the ultrafilter limit; all counted
outcomes are controlled in Hilbert direct sums or by telescoping.

The existing Cairn flexible-cut and polar-corner material can be
reused for B.2 and the elementary polar estimates; its soft
projection-cone material explains the useful choice of resolvent
densities. Those earlier results do **not** substitute for B.3–B.5
or C.2–C.3. The leaking-corner transport and reflected-Cheeger
material aligns with D's normalization checks but does not, on its
own, remove summable defects or produce the two-copy realization.
The missing mechanisms in those earlier nodes are precisely the
ones credited here to Liu. No new simplification of Liu's argument
is claimed on the basis of this correspondence.

Acceptance leaves the following separate obligations untouched:

- The minimum-rank/resolvent assembly and parameter limiting step
  in Liu Theorem 5.1 must be justified by its own route.
- Matching, exhaustion, exact internality, and all-trace normalization
  are separate mathematical steps, not consequences of schema
  compilation alone.
- Any nonhyperlinearity conclusion must include the actual group
  construction, the trace/normalization argument, and the final
  contradiction, with Liu and the earlier authors credited.
- This proof does not establish the stronger previously proposed
  fixed-gap decomposition of the *unperturbed* compressed generators.

Within the four stated interfaces, the all-rank, arbitrary-outcome,
noncommuting-resolvent, complex-matrix, and ambient-normalization
obligations have each been discharged above. This is the basis for
the four direct proof routes, rather than a blanket import of the
paper or a conversion of “no gap located” into “proved.”
