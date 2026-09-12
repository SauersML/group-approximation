# Aggregate Fourier rounding gives finite native dimension pressure

2026-09-08. Written finite-matrix proof. No execution, build, or
new Lean verification is asserted. The hyperlinearity endpoint
remains open.

All matrix traces and Hilbert--Schmidt norms are normalized by
the ambient dimension `n`. This proof first treats an arbitrary
approximate finite abelian table, then supplies literal native
relations realizing its hypotheses for the binary Leavitt group.

## 1. The dimension theorem

Let `A` be a finite abelian group of order `m>=2`, and let
`sigma:A->U(n)` satisfy

```text
sigma(1)=I,
max_(g,h in A) ||sigma(g)sigma(h)-sigma(gh)||_2<=epsilon,
max_(g!=1) |tr sigma(g)|<=a_0.                         (1)
```

Define `D=(11/2)sqrt(m)epsilon`. We prove

```text
n >= m (1-D)_+ / (sqrt(1+(m-1)a_0^2)+D)^2,            (2)
```

where `x_+=max(x,0)`. The denominator is positive. The estimate
is useful when the complete-table defect is small relative to
`m^(-1/2)`; it is still valid when its right side is zero.

## 2. Fourier errors can be summed before taking norms

For each character `chi` of `A`, form the contraction

```text
P_chi=(1/m) sum_(g in A) conjugate(chi(g)) sigma(g).
```

These need not be projections or commute. Nevertheless,

```text
sum_chi P_chi=I.                                      (3)
```

Vector-valued finite Parseval says that, for any matrices `X_g`,

```text
sum_chi ||(1/m) sum_g conjugate(chi(g)) X_g||_2^2
 =(1/m) sum_g ||X_g||_2^2.                            (4)
```

Apply this first to the inversion errors
`J_g=sigma(g^(-1))^*-sigma(g)`. The complete table and
`sigma(1)=I` give `||J_g||_2<=epsilon`. Changing the summation
index in `P_chi^*` therefore yields

```text
sum_chi ||P_chi^*-P_chi||_2^2<=epsilon^2.              (5)
```

For multiplication, set

```text
R_k=(1/m) sum_(g in A)
       (sigma(g)sigma(g^(-1)k)-sigma(k)).
```

Every `R_k` has norm at most `epsilon`. Grouping the product
defining `P_chi^2` according to `k=gh` gives the exact identity

```text
P_chi^2-P_chi=(1/m) sum_k conjugate(chi(k)) R_k.
```

Another application of (4) proves

```text
sum_chi ||P_chi^2-P_chi||_2^2<=epsilon^2.              (6)
```

The bounds (5)--(6) control the sum, rather than giving `m`
unrelated error estimates. This is what retains linear dimension
pressure in the group order.

## 3. Individually rounded projections with aggregate error

Put `B_chi=(P_chi+P_chi^*)/2`. These are self-adjoint
contractions. From (5),

```text
(sum_chi ||B_chi-P_chi||_2^2)^(1/2)<=epsilon/2.
```

For contractions `B,P`,
`B^2-P^2=B(B-P)+(B-P)P`, so
`||B^2-P^2||_2<=2||B-P||_2`. Applying the triangle inequality
in the Hilbert direct sum over characters, (5)--(6) imply

```text
(sum_chi ||B_chi^2-B_chi||_2^2)^(1/2)
 <=epsilon+3epsilon/2=5epsilon/2.                    (7)
```

Let `Q_chi=1_([1/2,infinity))(B_chi)`. For a real scalar `x`,

```text
|x-1_([1/2,infinity))(x)|<=2|x^2-x|.
```

Spectral calculus, (7), and the preceding symmetrization estimate
give

```text
(sum_chi ||Q_chi-P_chi||_2^2)^(1/2)
 <=5epsilon+epsilon/2=11epsilon/2.                   (8)
```

Each `Q_chi` is an actual projection in `M_n`. We make no
claim that different `Q_chi` commute or are orthogonal, or that
their sum is a projection. None of these properties is needed
in the next step.

## 4. Projection ranks convert the aggregate estimates to dimension

Set `p_chi=tr P_chi` and `q_chi=tr Q_chi`. The normalized
trace has norm one on the normalized-HS Hilbert space. Thus (8)
implies

```text
||q-p||_(ell^2)<=11epsilon/2,
sum_chi q_chi>=1-(11/2)sqrt(m)epsilon=1-D.             (9)
```

The second inequality uses (3) and Cauchy--Schwarz on the `m`
trace errors. Ordinary Fourier Parseval and (1) also give

```text
||p||_(ell^2)^2=(1/m) sum_g |tr sigma(g)|^2
 <=(1+(m-1)a_0^2)/m.
```

Consequently

```text
sum_chi q_chi^2
 <=(sqrt(1+(m-1)a_0^2)+D)^2/m.                       (10)
```

If `k_chi` is the integer rank of `Q_chi`, then
`q_chi=k_chi/n` and `k_chi^2>=k_chi`. Hence

```text
q_chi^2>=q_chi/n.
```

Sum this inequality and use (9)--(10). Since the total trace
is nonnegative, it follows that

```text
(1-D)_+/n <= sum_chi q_chi^2
          <=(sqrt(1+(m-1)a_0^2)+D)^2/m.
```

This is (2). When `epsilon=0`, it reads
`n>=m/(1+(m-1)a_0^2)`. With all nonidentity traces zero, it
becomes `n>=m`, attained by the exact regular representation
of `A`. Merely viewing the `m` group matrices as orthonormal
vectors in `M_n` would only give `n^2>=m`.

## 5. A growing packet of literal native Leavitt relations

Let `R=L_(F_2)(1,2)` and `H=R^x`, with the native generators
`c,b_1,b_2,b_3`. For `r>=1`, choose a power of two `d>2r`.
In the degree-zero matrix algebra `M_d(F_2)` inside `R`, put
an independent block

```text
J=[[0,1],[1,1]]
```

on each of `r` disjoint coordinate pairs, and identity on all
other coordinates. Since `J` has order three, these commuting
blocks generate an embedded subgroup `A_r=(C_3)^r`, of order
`m=3^r`.

Every nonidentity element of `A_r` is conjugate in `H` to the
native `c`. Here are the module details. If it has `k>0`
nontrivial blocks, swap the coordinates in any inverse block
to replace `J^(-1)` by `J`. Its moving right module is then
`R^k` on each of the two companion coordinates; apply the same
prefix-code isomorphism `R^k~=R` to both coordinates. Scalar
entries in `J` ensure that these maps intertwine its action.
The fixed summand is `R^(d-2k)` and has positive rank, because
`d>2r`. Compress it to `R` as well.

The native three-cycle on `R^3` splits into its fixed module
`R(1,1,1)` and the companion action on the rank-two sum-zero
module. Over `F_2` these summands are complementary, and the
companion action is `J` up to scalar change of basis. Both
actions therefore have the same fixed-plus-companion form.
The resulting intertwiner, transported through their prefix
identifications with the right module `R`, is left multiplication
by a unit of `R`. This proves the asserted conjugacy in `H`.
All module compressions use positive ranks; there is no
identification of a zero fixed summand with a nonzero one.

A complete binary prefix code with `k` leaves gives the
isomorphism `R^k~=R`: the maps use its real prefixes and ghost
prefixes, whose products are the matrix-unit identities and
whose range idempotents sum to one. Such a code exists for
each positive `k`, by successively splitting leaves. Thus the
conjugacy construction is finite algebraic data.

Choose a native word `w_a` for each `a in A_r`, with `w_1`
the empty word, and a native conjugator word `v_a` for `a!=1`
such that `a=v_a c v_a^(-1)` in `H`. These words exist by
[native generation](../binary-leavitt-units-generated-by-c3-and-c2-cubed.md).
Use the following literal rows, without simplifying by factor
relations during matrix evaluation:

```text
rho_(a,b)=w_a w_b w_(ab)^(-1)       (a,b in A_r),
theta_a=w_a v_a c^(-1) v_a^(-1)    (a!=1).           (11)
```

Each row is true in `H`. The list has at most `m^2+m-1`
rows. For any unitary evaluation with defect at most `epsilon`
on this list, set `sigma(a)=w_a(C,B)`. The first rows give
exactly the complete-table hypothesis in (1). The second rows
give

```text
||sigma(a)-V_a C V_a^*||_2<=epsilon,
|tr sigma(a)|<=|tr C|+epsilon        (a!=1).          (12)
```

No exact order-three or second-factor laws are needed of the
evaluated tuple for this inference: the prescribed empty word
still evaluates to `I`, all matrices are unitary, and the rows
are literal products. In particular it applies to the existing
frozen `24k` models, where `tr C=0` already holds.

Equations (2) and (12) prove the native dimension bound with
`m=3^r` and `a_0=|tr C|+epsilon`.

## 6. A simple quantitative regime and its precise scope

Suppose

```text
|tr C|<=epsilon<=1/(32 sqrt(m)),       m=3^r.
```

Then `a_0<=2epsilon`, so `(m-1)a_0^2<=1/256`, while
`D<=11/64`. As `sqrt(1+1/256)<65/64`, (2) gives

```text
n >= m (53/64)/(19/16)^2
   = (212/361)m > m/2.                              (13)
```

This is dimension pressure from an explicit family of native
finite tests. The subgroup and packet both grow with `r`.
The word representatives and conjugators have finite lengths;
no practical bound on their compiled native lengths is claimed.
The result is neither a uniform lower bound on defect for one
fixed packet nor a dimension upper bound for full microstates.
It does not decide their existence.

No simultaneous exactification of all Fourier projections was
used. The elementary matrix theorem in Sections 1--4 is
independent of a character-classification theorem or a finite-group
stability theorem. The native application uses only finite
subgroups, explicit module conjugacy, and native generation.
