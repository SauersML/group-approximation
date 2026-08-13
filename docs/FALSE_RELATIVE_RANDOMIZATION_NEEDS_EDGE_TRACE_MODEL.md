# Repeated-block randomization does not create the edge trace model

Date: 2026-08-13

## 1. Outcome

The one-orbit parity endpoint can be embedded in the untwisted even-edge
double

```text
R_even=L(J) *_L(K_0) L(J),                            (RRM1)
```

where both `J` and `K_0` are residually finite.  A natural proposal is:

1. choose finite-dimensional vertex representations whose restrictions to
   `K_0` contain very large repeated blocks;
2. conjugate the second vertex by a Haar unitary in the commutant of the
   repeated edge representation; and
3. use relative random-matrix asymptotic freeness to recover `(RRM1)`.

Step 2 can create relative freeness only after the finite models already
approximate the inclusion

```text
L(K_0) subset L(J)                                    (RRM2)
```

with its canonical conditional expectation.  Multiplicity amplification
does not manufacture that relative trace data.  For regular finite-quotient
blocks, the missing data is exactly subgroup separability of `K_0` in `J`,
or equivalently residual finiteness of the Schreier action `J` on `J/K_0`.
The Kun--Thom orbit used here is nonsofic, so this quotient-block strategy is
impossible even with arbitrary direct sums and multiplicities.

For arbitrary nonmonomial matrix blocks, the remaining hypothesis is a
genuinely new relative-embedding/conditional-expectation theorem.  Calling
the commutant large does not prove it.

## 2. The expectation test in a finite quotient

Let

```text
q:J->Q
```

be a finite quotient and put `H=q(K_0)`.  In the left regular representation
of `Q`, the trace-preserving expectation satisfies

```text
E_(L(H))(lambda_Q(q(j)))
 =lambda_Q(q(j))     if q(j) in H,
 =0                  otherwise.                       (RRM3)
```

The canonical expectation in the source is

```text
E_(L(K_0))(lambda_J(j))
 =lambda_J(j)        if j in K_0,
 =0                  otherwise.                       (RRM4)
```

For `j notin K_0`, a false membership `q(j) in q(K_0)` therefore creates
the exact error

```text
||E_(L(H))(lambda_Q(q(j)))||_2=1.                     (RRM5)
```

No matrix multiplicity changes `(RRM5)`: tensoring the regular block with
an identity multiplies both the numerator and denominator of the normalized
trace by the same amount.

## 3. Weighted repeated blocks are still separability

At stage `n`, allow finitely many quotients `q_(n,r):J->Q_(n,r)` with
dimension weights `mu_(n,r)`, summing to one.  The squared expectation error
for `j notin K_0` is

```text
Err_n(j)^2
 =sum_r mu_(n,r) 1_(q_(n,r)(j) in q_(n,r)(K_0)).      (RRM6)
```

Suppose `(RRM6)` tends to zero for every fixed `j notin K_0`.  Enumerate

```text
J minus K_0={j_1,j_2,...}.
```

For a fixed `m`, the union bound gives

```text
Prob_r[there exists i<=m:
       q_(n,r)(j_i) in q_(n,r)(K_0)]
 <=sum_(i<=m) Err_n(j_i)^2 ->0.                       (RRM7)
```

For large `n`, some positive-weight quotient separates all
`j_1,...,j_m` from `K_0`.  Taking successive product quotients yields a
sequence `q_m` with

```text
intersection_m K_0 ker(q_m)=K_0.                      (RRM8)
```

Equation `(RRM8)` is exactly closure of `K_0` in the profinite topology of
`J`.  It also makes the finite Schreier actions

```text
J/(K_0 ker(q_m))                                      (RRM9)
```

converge locally to `J/K_0`.  Hence the Schreier action is residually finite
and therefore sofic.

In the parity construction `K_0` has index two in `K`, and the natural
two-sheeted factor map

```text
J/K_0 -> J/K isomorphic G/Gamma                         (RRM9a)
```

is `J`-equivariant.  A sofic action has sofic finite factors.  The action
on `G/Gamma` is the Kun--Thom nonsofic coset action, so `J/K_0` cannot be
sofic and `(RRM8)` cannot hold.

Thus weighted quotient blocks, arbitrary repetitions, and highly uneven
multiplicities do not weaken the obstruction.

## 4. What commutant randomization can prove

Suppose one has already constructed matrix inclusions

```text
B_n subset A_n subset M_(d_n)                         (RRM10)
```

which converge in all required mixed moments to `(RRM2)` and whose
trace-preserving expectations `E_(B_n)` converge to `E_(L(K_0))`.  If the
finite-dimensional decomposition

```text
B_n isomorphic directSum_r (M_(e_(n,r)) tensor 1_(m_(n,r)))
```

has sufficiently large multiplicities `m_(n,r)`, Haar unitaries in
`B_n'` are a plausible tool for making two copies of `A_n` asymptotically
free over `B_n`.

But this theorem starts with `(RRM10)` and expectation convergence.  It
does not construct them.  Amplifying any candidate block increases the
commutant multiplicities while leaving every relative moment and every
expectation error unchanged.  Therefore amplification can improve the
randomization step but cannot solve the edge-embedding step.

## 5. Exact surviving theorem

The quotient-block version is closed by Sections 2--3.  The live
nonmonomial target is:

> Construct matrix microstates for the inclusion
> `L(K_0) subset L(J)` which approximate the canonical conditional
> expectation and admit enough common multiplicity for relative
> randomization, while retaining the negative central character.

This is a relative trace-model theorem, not merely an asymptotic-freeness
theorem.  The existing no-go results further show:

* exact finite-dimensional representations of the twisted vertex matching
  problem kill the central sign;
* finite quotient parity models would make the nonsofic Schreier action
  sofic; and
* matrix amplifications of the canonical regular vertex have a uniform
  twisted-innerness gap.

Consequently the required models, if they exist, must be genuinely
nonliftable and nonmonomial already at the vertex-edge inclusion.  Proving
their existence would finish the one-orbit parity route; repeated-block Haar
randomization would then be a final assembly tool rather than the source of
the missing geometry.
