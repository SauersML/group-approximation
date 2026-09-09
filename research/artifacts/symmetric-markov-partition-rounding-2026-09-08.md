# Reversible Markov near-idempotents round to partition expectations

Date: 2026-09-08. Written proof; no computation is used.

## 1. Statement and normalization

Let `Omega` be finite, and give every atom a strictly positive
probability mass `mu_i`, with `sum_i mu_i=1`. Let `K` have
nonnegative entries, row sums one, and detailed balance

```text
w_ij := mu_i K_ij = mu_j K_ji = w_ji.
```

We work over complex-valued functions. Define

```text
||f||_2^2 = sum_i mu_i |f_i|^2,
delta = ||K^2-K||_(infinity->2),
b(S) = sum_(i in S,j outside S) w_ij,
E_K(f) = <f,(I-K)f>
       = (1/2)sum_(i,j) w_ij |f_i-f_j|^2.
```

The operator `K` is a contraction on both `L^infinity` and
`L^2(mu)`, is self-adjoint on `L^2(mu)`, and preserves `mu`.
Its eigenvalues may be negative. No positivity as a Hilbert-space
operator is assumed or needed.

There exists a partition `Pi` of `Omega` such that the conditional
expectation

```text
(E_Pi f)_i = [sum_(j in P) mu_j f_j]/mu(P)   for i in P in Pi
```

satisfies

```text
||K-E_Pi||_(infinity->2) <= min{2,750 delta^(1/5)}.       (1)
```

No constant depends on the atom masses or the size of `Omega`.
For `0<delta<=1`, the proof constructs a partition with total
boundary

```text
beta := sum_(P in Pi) b(P)
 <= [2+12sqrt(3c)]delta^(2/5) < 25delta^(2/5),
c=2/sqrt(pi),                                           (2)
```

and, for every `P in Pi`,

```text
S subset P, mu(S)<=mu(P)/2  =>  b(S)>=mu(S)/36.           (3)
```

The boundaries in (2)--(3) always refer to the original `K`.
In particular, (3) is an ambient expansion property; it is not
an assertion about the induced kernel inside `P`.

The only imported analytic estimate below is the complex commutative
little-Grothendieck theorem. The construction is related to the
set-repair and partition step of
[Gabor Kun, *On sofic approximations of Property (T) groups*,
Theorem 3](https://arxiv.org/html/1606.04471v5).
Kun treats bounded-degree regular graphs. Here a different
localization step handles arbitrary transition weights, and the
variance argument uses the original kernel without graph rewiring.
All these weighted steps are proved below.

## 2. Localization without compression

Assume first `0<delta<=1`, put `D=K^2-K`, and set

```text
q=delta^(2/5),       c=2/sqrt(pi),       eta=c delta^(4/5).
```

The commutative little-Grothendieck theorem gives a probability
measure `nu` on `Omega` with

```text
||Df||_2 <= c delta [sum_i nu_i |f_i|^2]^(1/2)            (4)
```

for all complex `f`. The precise constant is stated in
[Kalenda--Peralta--Pfitzner, *On optimality of constants in the
Little Grothendieck Theorem*, Theorem A](https://arxiv.org/html/2002.12273),
arXiv:2002.12273v3.

Define

```text
B={i: nu_i>mu_i/q}.
```

Since `nu` has total mass one, `mu(B)<=q`. If `f` is supported
outside `B`, (4) gives

```text
||Df||_2 <= c delta q^(-1/2)||f||_2 = eta||f||_2.        (5)
```

This controls the original operator on specified inputs. We never
replace `K` by its compression to `Omega\B`, and never renormalize
`mu` on a remaining set. Outputs in (5) are measured on all of
`Omega`; they need not be supported outside `B`.

## 3. Repair one set using weighted coarea

For every `T subset Omega\B`, let `f=K 1_T`. Stochasticity,
stationarity, and (5) give

```text
0<=f<=1,       ||f||_1=mu(T),       ||f||_2<=sqrt(mu(T)),
||Kf-f||_2=||D 1_T||_2<=eta sqrt(mu(T)),
E_K(f)<=||f||_2||f-Kf||_2<=eta mu(T).                    (6)
```

There is a threshold `t in (1/3,2/3)` such that `U={f>t}`
satisfies

```text
b(U) <= 3sqrt(3eta) mu(T),
mu(U symmetric_difference T) <= 18 b(T).                (7)
```

Here is the full boundary estimate. Put `A={f>1/3}` and
`g=min{2/3,max{1/3,f}}`. Then `mu(A)<=3mu(T)`. By weighted
coarea,

```text
integral_(1/3)^(2/3) b({f>t}) dt
 = (1/2)sum_(i,j) w_ij |g_i-g_j|.
```

Every nonzero summand has at least one endpoint in `A`. The
total ordered edge weight incident to `A` is at most `2mu(A)`.
Clipping is 1-Lipschitz, so Cauchy--Schwarz and (6) imply

```text
integral_(1/3)^(2/3) b({f>t}) dt
 <= (1/2)[2mu(A)]^(1/2)
            [sum_(i,j) w_ij |f_i-f_j|^2]^(1/2)
 <= sqrt(3eta) mu(T).
```

An interval of length `1/3` therefore contains a threshold
with the first bound in (7). The level-set boundary is a
finite step function, so the threshold can be taken strictly
inside the interval.

For any such threshold, every point of `U symmetric_difference T`
has `|f-1_T|>=1/3`. Jensen's inequality for the stochastic
rows, followed by stationarity, gives

```text
||K1_T-1_T||_2^2
 <= sum_(i,j) w_ij |1_T(j)-1_T(i)|^2
 = 2b(T).
```

Consequently

```text
mu(U symmetric_difference T)
 <= 9||f-1_T||_2^2 <= 18b(T),
```

which proves the second bound in (7).

## 4. Peel sets of minimum mass to obtain an actual partition

Set `gamma=1/36`. Start with remaining set `R=Omega\B`.
Every atom of `B` will be a singleton block. While `R` is
nonempty, do the following.

If every nonempty `T subset R` has `b(T)>=gamma mu(T)`,
use all of `R` as the last block and stop. Otherwise choose a
nonempty `T subset R` of MINIMUM `mu`-mass among the sets with

```text
b(T)<gamma mu(T).
```

There are only finitely many subsets, so the minimum exists.
Apply (7), and create the next block `P=U intersect R`.
Because `T subset R`, we have

```text
mu(U symmetric_difference T)<mu(T)/2,
mu(T)/2 < mu(P) < 3mu(T)/2.                              (8)
```

Thus the block is nonempty. Remove it from `R` and continue;
the process terminates after finitely many steps.

If `S subset P` and `mu(S)<=mu(P)/2`, then (8) gives
`mu(S)<mu(T)`. Such an `S` was contained in `R` at the time
`T` was chosen. Minimum mass therefore forces
`b(S)>=gamma mu(S)`. This also holds for the possible final
block by its defining condition. For a singleton block it is
vacuous except for the empty set. We have proved (3) for
EVERY block of the resulting partition.

It remains to bound the total boundary of the partition.
Regard `w_ij` for `i<j` as an unoriented edge weight. A
cross-block edge whose endpoints are outside `B` has an
endpoint assigned at an earlier peeling step. At that step
the earlier endpoint belongs to `U`, whereas the later
endpoint, still in `R`, does not belong to `U`; otherwise
it would have joined the same block. Thus the edge crosses
that step's `U`. Every such cross-block edge is charged at
least once by `sum_steps b(U)`.

The total unoriented weight of all edges touching `B` is at
most `sum_(i in B,j)w_ij=mu(B)`. This also covers the extra
cuts made by splitting `B` into singletons. Since summing the
block boundaries counts every cross-block edge twice,

```text
beta <= 2mu(B)+2sum_steps b(U).
```

By (7)--(8),

```text
sum_steps b(U)
 <= 3sqrt(3eta) sum_steps mu(T)
 <= 6sqrt(3eta) sum_steps mu(P)
 <= 6sqrt(3eta).
```

Therefore

```text
beta <= 2q+12sqrt(3eta)
      = [2+12sqrt(3c)]delta^(2/5)
      < 25delta^(2/5).                                 (9)
```

This proves (2). The argument charges cuts against the
original edge weights, even when a repaired set `U` overlaps
previously removed blocks. It uses no assumption that `U`
itself is contained in the current remaining set.

## 5. A defective Cheeger bound with exterior edges retained

Let `P` be any block satisfying (3), and let a real nonnegative
function `h` be supported on a subset of `P` of mass at most
`mu(P)/2`. Every positive superlevel set of `h^2` satisfies
(3). Integrating that inequality and using weighted coarea,

```text
gamma||h||_2^2
 <= integral_0^infinity b({h^2>t})dt
 = (1/2)sum_(i,j)w_ij |h_i^2-h_j^2|
 <= (1/2)[sum w_ij|h_i-h_j|^2]^(1/2)
            [sum w_ij|h_i+h_j|^2]^(1/2)
 <= sqrt(2E_K(h))||h||_2.
```

The last step uses
`sum w_ij|h_i+h_j|^2<=4||h||_2^2`. Hence

```text
||h||_2^2 <= (2/gamma^2)E_K(h).                         (10)
```

Now let `g` be real with `||g||_infinity<=1`. Choose a
weighted median `m_P` of its values on `P`, so that both
`{i in P:g_i>m_P}` and `{i in P:g_i<m_P}` have mass at most
`mu(P)/2`. The median lies in `[-1,1]`. Extend the functions

```text
h_+=(g-m_P)_+ 1_P,       h_-=(m_P-g)_+ 1_P
```

by zero outside `P`. Their supports meet the hypothesis of
(10). For pairs of points inside `P`, positive and negative
parts satisfy

```text
|a_+-b_+|^2+|a_--b_-|^2 <= |a-b|^2.
```

On an edge leaving `P`, the sum of their squared values at
the endpoint in `P` is `|g_i-m_P|^2<=4`. It follows that

```text
E_K(h_+)+E_K(h_-)
 <= E_(internal,P)(g)+4b(P),
E_(internal,P)(g)=(1/2)sum_(i,j in P)w_ij|g_i-g_j|^2.
```

The block average minimizes squared distance to a constant.
Applying (10) to the two parts therefore gives

```text
sum_(i in P)mu_i |g_i-(E_Pi g)_i|^2
 <= (2/gamma^2)[E_(internal,P)(g)+4b(P)].                (11)
```

For a complex contraction `g`, apply (11) to its real and
imaginary parts and sum over blocks. Their Dirichlet forms
sum to `E_K(g)`, and the internal energies are bounded by
the full energy. We obtain

```text
||g-E_Pi g||_2^2
 <= (2/gamma^2)[E_K(g)+8beta].                          (12)
```

The boundary term in (12) is the explicit cost of using
ambient expansion rather than an internal spectral gap.
No claim that compression preserves the spectral defect
or the invariant measure has entered this estimate.

## 6. Control output variance and block means separately

Let `x` be any complex contraction and put `g=Kx`. Then
`g` is a contraction and

```text
E_K(Kx)=<Kx,Kx-K^2x>=-<Kx,Dx><=delta.                  (13)
```

The energy is real and nonnegative; its upper bound follows
from Cauchy--Schwarz, `||Kx||_2<=1`, and the definition of
`delta`. In particular, (13) does not require the spectrum
of `K` to lie in `[0,1]`. Equation (12) now shows

```text
||(I-E_Pi)K||_(infinity->2)
 <= (sqrt(2)/gamma)sqrt(delta+8beta).                   (14)
```

For the other component, detailed balance cancels internal
edges in a block average exactly:

```text
(E_Pi(K-I)x)|_P
 = (1/mu(P))sum_(i in P,j outside P)w_ij(x_j-x_i).
```

Its absolute value is at most `2b(P)/mu(P)`. Since
`b(P)<=mu(P)`, summing squared values yields

```text
||E_Pi(K-I)x||_2^2
 <= 4sum_(P in Pi) b(P)^2/mu(P)
 <= 4beta.                                             (15)
```

Combine (14)--(15) with

```text
K-E_Pi=(I-E_Pi)K+E_Pi(K-I).
```

Using `gamma=1/36`, (9), and `delta<=delta^(2/5)` for
`0<delta<=1`, we get

```text
||K-E_Pi||_(infinity->2)
 <= 36sqrt(2delta+16beta)+2sqrt(beta)
 <= [36sqrt(402)+10]delta^(1/5)
 < 750delta^(1/5).                                     (16)
```

Both operators are contractions from `L^infinity` to `L^2`,
so the same partition also has distance at most two. This
proves (1) when `0<delta<=1`. For `delta>1`, any partition
has distance at most two, which is the minimum in (1).

If `delta=0`, then `K` is an orthogonal projection. A
function is fixed by `K` exactly when its Dirichlet form is
zero, hence exactly when it is constant on every connected
component of the undirected graph with edges `w_ij>0`.
Thus its range is that partition algebra and `K` is its
`mu`-preserving conditional expectation. This handles zero
defect without a limiting argument.

## 7. Exact matrix-channel realization and commutative range

For uniform `mu_i=1/n`, identify functions with diagonal
matrices and write `d(X)` for the vector of diagonal entries.
Define

```text
P_K(X)=diag(K(d(X))).
```

This is UCP, for example by Kraus operators
`sqrt(K_ij)E_ji` in the convention `sum v*Xv`.
Stochasticity and symmetry imply unitality, trace preservation,
and self-adjointness for normalized matrix `L^2`.

Taking the diagonal is a contraction from matrix operator norm
to function supremum norm, and every function is realized by
a diagonal matrix of the same norm. It follows exactly that

```text
||P_K^2-P_K||_(infinity->2)=||K^2-K||_(infinity->2),
||P_K-E_(A_Pi)||_(infinity->2)=||K-E_Pi||_(infinity->2),
A_Pi={diag(f): f is constant on every P in Pi}
    = direct_sum_(P in Pi) C I_(|P|).                   (17)
```

The expectation in (17) kills off-diagonal entries and
averages within each block. The rounded algebra remains
in `M_n(C)` and its multiplicities `|P|` are unrestricted.

More generally, let `P:M_n(C)->M_n(C)` be self-adjoint,
bistochastic, and UCP, with commutative range. A unitary
conjugation puts that range inside a maximal abelian algebra
`D` of diagonal matrices. Thus `E_D P=P`. Taking Hilbert-space
adjoints gives `P E_D=P`. Hence `P=E_D P E_D`, and its
restriction to `D` is a symmetric stochastic kernel. The
previous construction applies, proving (1) for every such
commutative-range channel. No pointwise near-fixing of `D`
is assumed.

In particular, a symmetric probability measure on ANY finite
group gives a symmetric stochastic convolution matrix, whether
or not the measure is central. It therefore admits (1) as a
function operator and as the associated matrix channel. This
proof selects a partition and does not assert that the
partition consists of subgroup cosets. The separate central
convolution theorem retains its stronger linear modulus and
normal-coset conclusion.

## 8. Exact scope of the classical argument

The result supplies full mixed-norm rounding for finite
reversible Markov kernels, not just a collection of expanding
components. Equations (14)--(15) produce closeness to a
single actual conditional expectation in the original space.

Several steps use commutativity in a way that needs a new
argument for general quantum channels:

- The level sets of a scalar function are genuine subsets,
  and threshold coarea uses positive edge weights between
  their common coordinate atoms.
- Intersecting `U` with the remaining set creates an exactly
  disjoint block while preserving the mass estimates in (8).
  The earliest-endpoint argument charges each new cut using
  the same scalar edges, independently of earlier cuts.
- Positive and negative parts about a scalar block median
  have disjoint supports and satisfy the pairwise energy
  inequality used in (11).
- Internal-flow cancellation in (15) controls the block
  averages by precisely the already charged exterior edges.

The theorem does not provide these operations for arbitrary
noncommuting physical projections or Kraus operators. It
does not establish general UCP rounding, native Kazhdan heat
rounding, a full-kernel matrix model, or nonhyperlinearity.

The probability weight from Grothendieck localization is
auxiliary throughout; it is never a replacement trace.
The estimates are uniform even when the stationary atom
weights are arbitrarily small.

Repository searches and the primary sources above were checked
on 2026-09-08. The written proof records a reusable scoped
theorem and makes no claim of priority. No code, graph check,
or Lean verification was run as part of writing this artifact.
