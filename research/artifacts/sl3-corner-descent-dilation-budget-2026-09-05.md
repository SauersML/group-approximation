# Canonical swap corners: the exact cost of restoring the actor

Date: 2026-09-05. Status: a proved obstruction to one proposed dimension
descent, not a nonhyperlinear-group construction. The general dilation
calculus is standard; the purpose here is to apply it with the correct
normalization to Cairn's canonical arithmetic swap model.

## 1. The attempted contradiction and the missing inheritance

In a hypothetical canonical matrix model of

```text
E_p = <SL_3(Z[1/p]), s | s^2=1, [s,SL_3(Z)]=1>,
```

the projection `q=(1+s)/2` has trace `1/2` and commutes with the lattice
algebra `B=L(SL_3(Z))`. Compressing to `q` therefore retains an exact
lattice representation in the ultraproduct. At the matrix level,
off-diagonal lattice blocks have vanishing normalized HS norm, and their
diagonal compressions can be changed by `o(1)` to unitaries. The two corner
traces are regular on the lattice because `tau(q b)=tau(b)/2` there.

If both corner sequences were flexibly close to genuine lattice
representations, their direct sum would be close to the original sequence.
This is the valid one-step observation behind the old outlier argument.

It does not produce two smaller models of `E_p`, or even one. On the
`q` corner the old involution becomes the identity, so it is no longer
balanced. More substantially, if `h=diag(p,1,p^{-1})` and `u=u_h`, the
compression `a=q u q` is not nearly unitary. With corner trace
`tau_q(x)=2 tau(x)`, canonicality gives

```text
tau_q(a^*a)=1/2,
tau_q(q-a^*a)=1/2.                                      (CBD1)
```

For example, `tau(q u^* q u)=1/4` follows by expanding in the two
distinct free involution lamps. Consequently every unitary `v` in the
same corner satisfies the elementary lower bound

```text
||a-v||_(2,q) >= 1-1/sqrt(2).                            (CBD2)
```

This already rules out literal compression followed by a vanishing
same-space perturbation. The full canonical spectrum gives a sharper
bound and determines how much extra dimension can help.

## 2. Exact finite-dimensional optimization

Let `A` be an `r x r` contraction with singular values
`1>=a_1>=...>=a_r>=0`, and fix `0<=k<=r`. Let `D_(r,k)` be the set of
upper-left `r x r` blocks of unitaries of size `r+k`. Then

```text
inf_(B in D_(r,k)) ||A-B||_(2,r)^2
  = (1/r) sum_(i=1)^(r-k) (1-a_i)^2.                    (CBD3)
```

For the lower bound, write the first block column of a unitary as
`[B; C]`, with `C` of size `k x r`. Unitarity gives
`I-B^*B=C^*C`, which has rank at most `k`. Thus the largest `r-k`
singular values of `B` equal one.

For completeness, the singular-value distance inequality used here is

```text
||A-B||_F^2 >= sum_i (a_i-b_i)^2,                        (CBD4)
```

with both lists in decreasing order. Indeed,
`Re Tr(A^*B)<=sum_i a_i b_i`: in singular-vector bases, bound the absolute
value of each product of change-of-basis entries by half the sum of their
squared absolute values. Each squared-entry matrix is doubly stochastic,
and the rearrangement inequality bounds its pairing with the two ordered
lists by `sum_i a_i b_i`. Expanding the squared Frobenius norm proves
`(CBD4)`, hence the lower bound in `(CBD3)`.

For attainment, write `A=U diag(a_i) V^*`. Replace the first `r-k`
diagonal entries by one and retain the last `k` entries. Each retained
entry `a_i` is the upper-left entry of the unitary rotation

```text
[ a_i              -sqrt(1-a_i^2) ]
[ sqrt(1-a_i^2)      a_i          ].
```

The direct sum of these rotations and the `r-k` scalar unit blocks acts
in dimension `r+k`. Multiplication on the left and right by
`diag(U,I_k)` and `diag(V^*,I_k)` gives the required compression and
attains the lower bound. For `k>=r` the infimum is zero.

This proves the exact optimization without assumptions on eigenvectors,
normality, or the surrounding arithmetic action.

## 3. Canonical arithmetic specialization

Let `P_n` be either spectral half of the rounded swap involution in a
canonical microstate sequence, let `H_n` represent `h`, and set

```text
r_n=rank(P_n),          A_n=P_n H_n P_n | ran(P_n).
```

The existing node `canonical-arithmetic-swap-fold-gram-is-arcsine` proves
the required law for `p=2`. Its normal-form argument is prime independent:
`hsh^{-1}s` is the product of two distinct free involution lamps, so every
nonzero power is nontrivial. Canonicality makes the fold's spectral measure
Haar on the circle. The two-projection decomposition then gives the arcsine
law for the Gram operator in the normalized half-dimensional corner.
Thus the same calculation applies to every prime, including `p>=11`.

To check the orientation explicitly, put `Q_n=H_n P_n H_n^*`. Conjugating
`A_n^*A_n=P_n H_n^* P_n H_n P_n` by `H_n` gives `Q_n P_n Q_n`.
The trace used for singular values is the corner trace, not the original
`d_n`-dimensional trace. Hence

```text
r_n/d_n -> 1/2,
mu_(A_n^* A_n) -> dx/(pi sqrt(x(1-x))),       0<x<1,
mu_(|A_n|) -> 2 da/(pi sqrt(1-a^2)),         0<a<1.      (CBD5)
```

For `k_n/r_n -> beta in [0,1]`, the largest `1-beta` fraction of singular
values starts at `a=sin(pi beta/2)`. The limiting law is continuous, so
the trimmed sums in `(CBD3)` converge, including at `beta=0,1`.
Putting `L=(pi/2)(1-beta)` yields the sharp limiting squared error

```text
F(beta) = (2/pi) integral_0^L (1-cos(theta))^2 dtheta
        = (2/pi) [(3/2)L - 2 sin(L) + (1/4)sin(2L)].     (CBD6)
```

In particular

```text
F(0)=3/2-4/pi,
F(beta)>0 for beta<1,
F(beta) ~ (pi^4/320)(1-beta)^5 as beta increases to 1.    (CBD7)
```

The first number is about `0.2267604553`, so the best same-corner
unitary approximation has limiting HS error about `0.4761937161`.
The expansion follows from `(1-cos(theta))^2=theta^4/4+O(theta^6)`.

Suppose a sequence of dilated unitaries approximates `A_n` with error
`o(1)`. If `k_n/r_n` had a subsequence bounded below one, a further
convergent subsequence and `(CBD6)` would give a strictly positive error.
Therefore `k_n >= (1-o(1))r_n`, and

```text
r_n+k_n >= (1-o(1))d_n.                                 (CBD8)
```

The dimension removed by splitting must asymptotically be restored even
to recover this single actor with vanishing compression error.

## 4. What this settles, and what it leaves open

The earlier statement that the original free-involution model
automatically propagates down a binary tree of corners is not justified.
Only the lattice restriction passes to the corners. The involution loses
balance, and the denominator actor has the positive compression defect
`(CBD1)`. Equations `(CBD3)--(CBD8)` show that allowing small flexible
padding does not repair the latter problem.

This is not a proof that arbitrary smaller arithmetic models cannot be
built. Such a construction could choose a new denominator actor far from
`P_n H_n P_n`, but it would need a new argument preserving all arithmetic
relations and the free-lamp moments. The calculation supplies neither such
an argument nor an obstruction to it. In particular the nonhyperlinear
target and the free-involution outlier exclusion remain open.

There is a second scope issue in the same old attempt: property (T)
provides a uniform gap for genuine unitary representations, including
the exact conjugation representation in a tracial ultraproduct. It does
not automatically give a uniform coordinate-level gap for the conjugations
defined by HS approximate representations. For
`v_d=diag(-1,1,...,1)`,

```text
||v_d-I||_(2,d)=2/sqrt(d),
||Ad(v_d)-I||_(op on HS_d)=2.
```

The matrix unit `e_12` gives the second equality. Thus coordinate relator
errors vanishing in normalized HS norm do not imply the operator-norm
control needed for that proposed spectral-gap transfer. No automatic
"robust Kazhdan projection" for those approximate actions is used here.

## Sources and novelty scope

The canonical arcsine computation is already in this repository. The
classical free-projection/principal-angle law is also discussed by
[Aubrun, Principal angles between random subspaces and polynomials in two
free projections](https://arxiv.org/abs/2109.06535). For context on standard
unitary dilations and finite defect numbers see
[Dey--Mukherjee, Higher Rank Numerical Ranges and Unitary
Dilations](https://arxiv.org/abs/2111.09249). The finite optimization is
proved above; its application here is recorded to correct the descent
argument, without claiming global novelty for the underlying linear algebra.

## Replay checks

Run `python experiments/corner_dilation_budget_check.py`. With seed
`20260905`, 96 finite dilation cases (including zero, unit, repeated, and
random singular spectra in independently rotated bases) attain `(CBD3)`
to error below `6.7e-16`; the constructed full unitaries have Frobenius
unitarity defect below `2.0e-15`. Independently sampled competitors do not
violate the lower bound beyond floating-point tolerance. Quadrature agrees
with `(CBD6)` to `4.9e-17`, and a 32768-point deterministic angle grid gives
the predicted six trimmed-spectrum costs to `1.3e-10`.

These are numerical checks of the formulas and normalization. The proof is
the argument above; the checks do not verify an arithmetic model, establish
nonhyperlinearity, or constitute Lean certification.
