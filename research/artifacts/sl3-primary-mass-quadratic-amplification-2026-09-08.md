# A conductor-independent quadratic bound on primary mass

2026-09-08. Written mathematical proof. All Hilbert--Schmidt norms and
matrix traces below are normalized by the full matrix dimension.

## 1. The qualitative input and its exact scope

Use the notation of
[the primary-sector audit](independent-kirillov-primary-sector-audit-2026-09-08.md).
For a fixed prime `p`, it proves:

> If genuine congruence representations `sigma_n` of `SL_3(Z)` admit
> unitary fixed-overlap intertwiners with errors tending to zero, the
> normalized dimension `q_n` of their nontrivial p-primary parts tends
> to zero.

There is no restriction on the conductor sequence or on the distribution
of representation multiplicities. At prime two the positive Fourier
formula is used on squares of a uniform pro-2 group, as required by
Boyarchenko--Sabitova, Theorem 2.8; for odd primes it is Theorem 2.6.
The primary source is [the authors' paper](https://arxiv.org/pdf/math/0608126).
The audit supplies the remaining measure and group arguments explicitly.

We show that this qualitative statement already implies `q<=K_p epsilon^2`.

## 2. Remove the coprime factor without losing uniform control

Let `kappa_D>0` be a Kazhdan constant for the chosen overlap generating
set. On the Hilbert--Schmidt space, the genuine unitary representation

```text
d: X -> sigma(hdh^(-1)) X sigma(d)^*
```

has invariant space consisting of exact intertwiners. Orthogonally
project `H` onto this space, obtaining `T` with

```text
||T-H||_2 <= epsilon/kappa_D.                            (1)
```

Write `sigma_p` for the representation of the p-primary factor on the
same `d`-dimensional space, with its commuting coprime factor set equal
to the identity. The exact Chinese remainder argument in Section 1 of
the primary audit gives

```text
T sigma_p(k)=sigma_p(hkh^(-1)) T       (k in D_p).       (2)
```

Specifically, if the primary conductor divides `p^a`, lift `k` modulo
`p^(a+2)` and lift the identity modulo `m`. Conjugation by `h` can lose
two digits, so both required reductions still agree modulo `p^a`.
The coprime reductions on both sides are the identity. Consequently

```text
sup_(k in D_p) ||H sigma_p(k)-sigma_p(hkh^(-1))H||_2
 <= 2 epsilon/kappa_D.                                 (3)
```

The same bound holds for the fixed discrete overlap generators. In
particular, `sigma_p` remains an exact representation of `C` factoring
through the same p-primary quotient; its invariant projection is `P`.

## 3. A fixed lattice generator detects the entire primary mass

Fix a Kazhdan generating set `S_C` of `C` with constant `kappa_C>0`.
Apply its estimate to the genuine left multiplication representation
`X -> sigma_p(c)X` on `M_d`, with unit vector `I`. Its invariant
projection sends `I` to `P`, so `||I-P||_2^2=q`. Thus some `s in S_C`
satisfies

```text
||sigma_p(s)-I||_2^2 >= kappa_C^2 q.                    (4)
```

This uses invariant dimension, not a bound on the trace of any particular
irreducible character. It includes arbitrary primary multiplicities.

## 4. A doubling that makes every relevant trace nonnegative

Set

```text
lambda(c)=sigma_p(c) direct-sum I_d,
V=H direct-sum I_d,
tau(c)=lambda(c) tensor conjugate(lambda(c)),
W=V tensor conjugate(V).
```

For any unitary `R`, write `z=tr(R)`. The doubled, conjugate-tensored
matrix has normalized trace

```text
t=|(1+z)/2|^2 in [0,1].
```

The elementary identities

```text
t-Re(z)=|1-z|^2/4 >=0,
t <= (1+Re(z))/2
```

give respectively

```text
2(1-t) <= ||R-I||_2^2,
1-t >= ||R-I||_2^2/4.                                 (5)
```

For an overlap generator use
`R=H sigma_p(d)H^* sigma_p(hdh^(-1))^*`. The corresponding residual
for `(tau,W)` is exactly the doubled, conjugate-tensored residual.
For the generator selected in (4), the character of `tau` satisfies

```text
tr(tau(s)) <= 1-kappa_C^2 q/4.                          (6)
```

The trivial summand prevents a scalar phase from disappearing under
conjugate tensoring. Both the target character and each source residual
now have nonnegative real normalized trace.

## 5. Amplification contradicts a failed quadratic bound

Suppose no finite constant in `(PQG)` exists. Choose examples with
`q_n>0` and `epsilon_n^2/q_n ->0`. Put `r_n=ceil(1/q_n)` and form

```text
rho_n=tau_n^(tensor r_n),       J_n=W_n^(tensor r_n).
```

These are genuine representations through the same finite p-primary
quotients, in larger finite matrix dimensions. For `0<=t<=1`,
`1-t^r<=r(1-t)`. Therefore (3) and (5) imply, on every fixed overlap
generator,

```text
||J_n rho_n(d)-rho_n(hdh^(-1))J_n||_2^2
 <= 4 r_n epsilon_n^2/kappa_D^2
 <= 8 epsilon_n^2/(kappa_D^2 q_n) ->0.                 (7)
```

The qualitative primary theorem now says that the nontrivial primary
dimension of `rho_n` tends to zero. Thus every fixed lattice generator
has squared displacement at most four times that dimension and tends
to the identity in normalized Hilbert--Schmidt norm.

On the other hand, pass to a subsequence for which the generator in (4)
is one fixed `s`. Equation (6) gives

```text
tr(rho_n(s)) <= (1-kappa_C^2 q_n/4)^(r_n)
             <= exp(-kappa_C^2/4) <1,                 (8)
```

contradicting that conclusion. Hence the uniform finite constant exists.

The contradiction does not compute its value. The theorem uses exact
lattice representations throughout and supplies no exactification
theorem for an arbitrary approximate lattice representation. Its gain is
the removal of every conductor-depth loss on the genuine sector.

## 6. Finite tracial coordinate algebras

The canonical qualitative prerequisite is stated for arbitrary finite
tracial von Neumann algebras, and the quantitative proof has the same
scope. In a coordinate algebra `(M,tau)`, the primary invariant
projection is the finite-group average `P`; left multiplication on
`L^2(M,tau)` projects the vector `1` to `P`. Orthogonal projection onto
the overlap intertwiners is still a convex average of unitary left and
right multiplication. Chinese remainder extraction is unchanged.

Use `M direct-sum M` with the equally weighted trace for the trivial
summand, tensor with its conjugate tracial algebra, and take finite
spatial tensor powers. Normalized traces multiply, so equations (5)--(8)
remain identical. The transformed algebras are finite and carry
normalized faithful traces. The qualitative theorem applies to them
and gives the same contradiction. Thus no matrix-dimension restriction
enters the constant in the primary-mass inequality.
