# Kernel geometry, finite syndrome cost, and a uniformity criterion

This continues the exact syndrome synthesis analysis. It supplies full
finite-dimensional proofs and explicit certificate replays. It does not
prove quantum PCP. The rank-one resolution problem is classical frame
scalability; see [Kutyniok, Okoudjou, and Philipp, *Scalable Frames and
Convex Geometry*, Proposition 3.4](https://www.norbertwiener.umd.edu/Education/IMA2015/t3/ScalabilityAndConvexityRevised.pdf).
Cone separation and frame normalization are standard tools. No priority or
novelty claim is made for them or for this specialization. The contribution
to this repository is the precise syndrome criterion and its verification
and use in the open route.

## 1. Remove the numerical constant while retaining the kernels

Fix positive terms `h_1,...,h_m` on a nonzero finite-dimensional space `H`.
Fix energy neighborhoods and write `A_a=sum_(b in N(a))h_b`. As before,
`F` is the family of fault sets for which the terms outside the set have a
nonzero common kernel. Define the *input* support subspaces

```text
V_S = intersection_(a in S) ran(A_a),           for S in F.
```

The intersection for `S=empty` is `H`. These are different from the output
common kernels defining `F`; both are needed.

**Theorem 1 (finite-cost criterion).** An unrestricted exactifying
instrument satisfying `F_a<=C_0 A_a` for some finite `C_0>=0` exists if and
only if there are positive matrices `T_S`, indexed by feasible labels, with

```text
ran(T_S) subset V_S,          sum_(S in F) T_S = I.           (Resolution)
```

**Necessity.** Use the joint effects `E_S` of the instrument. The primal
criterion gives zero effects at infeasible labels. For `a in S`,
`0<=E_S<=F_a<=C_0 A_a`. If `v in ker A_a`, positivity implies
`E_S v=0`; thus `ran(E_S) subset ran(A_a)`. Taking `T_S=E_S` gives
(Resolution).

**Sufficiency.** Set `E_S=T_S` for feasible labels and zero otherwise. Its
marginal `F_a` has range in `ran(A_a)` and satisfies `0<=F_a<=I`. Let `P_a`
be the orthogonal projection onto `ran(A_a)`. A positive contraction
supported there satisfies `F_a<=P_a`. If `A_a!=0`, let `delta_a>0` be its
least positive eigenvalue. Then

```text
F_a <= P_a <= A_a/delta_a.
```

If `A_a=0`, the support condition forces `F_a=0` instead. There are finitely
many indices, so a finite common constant exists. The earlier primal
theorem supplies the conditional exactifier on the original space `H`.

This distinguishes two failures. The geometry can rule out every finite
local constant. When the geometry allows a resolution, shrinking positive
eigenvalues can still prevent a uniform constant across instances.

## 2. A complete alternative for the infinite-cost case

Let `C` be the cone of all sums of positive matrices supported on the
`V_S`, without imposing sum `I`.

**Theorem 2.** Exactly one of the following holds:

1. (Resolution) exists, and hence a finite local constant exists.
2. There are positive `X_a` supported on `ker A_a` and Hermitian `Y` such
   that `Tr(Y)>0` and `sum_(a in S) X_a >= Y` for every feasible `S`.

In alternative 2, `sum_a Tr(X_a A_a)=0`, so these matrices are an
infinite-cost certificate for the earlier weak dual inequality.

**Proof of closure and separation.** The cone `C` is closed. Indeed, if
`Z_n=sum_S T_(n,S)` converges, positivity bounds each `Tr(T_(n,S))` by the
bounded sequence `Tr(Z_n)`. Finitely many compact bounded matrix sets give
a subsequence on which every summand converges. Its limits remain positive
and supported on their respective closed subspaces, giving a decomposition
of the limiting `Z`.

Suppose `I not in C`, and let `Z_*` be a nearest point of this closed
convex cone to `I` in Hilbert--Schmidt norm. Put `Y_0=I-Z_*`.
The nearest-point inequality gives
`Tr[Y_0(Z-Z_*)]<=0` for all `Z in C`. Taking `Z=0` and `Z=2Z_*`
shows `Tr(Y_0 Z_*)=0`. Consequently

```text
Tr(Y_0 Z) <= 0 for all Z in C,
Tr(Y_0) = ||Y_0||_HS^2 > 0.
```

Testing rank-one positive matrices supported in `V_S` shows that the
compression of `Y_0` to every `V_S` is nonpositive.

**Convert this separation to the earlier dual format.** Let `D=dim H`,
`epsilon=Tr(Y_0)/(2D)>0`, and `Y=Y_0-epsilon I`. Its trace is still
positive, and its compression to each `V_S` is at most `-epsilon I`.
Let `K_a` project onto `ker A_a`, and put `K_S=sum_(a in S)K_a`.
Positivity gives `ker K_S=V_S`. On `V_S` perpendicular, `K_S` has a
positive spectral lower bound `kappa_S` whenever that space is nonzero.

Write `u+v` with `u in V_S`, `v` perpendicular to `V_S`, and `L=||Y||`.
For a scalar `t>=0`,

```text
<u+v,(t K_S-Y)(u+v)>
 >= epsilon ||u||^2 - 2L ||u|| ||v|| + (t kappa_S-L)||v||^2
 >= (t kappa_S-L-L^2/epsilon)||v||^2.
```

Choose one finite `t` at least `(L+L^2/epsilon)/kappa_S` for all the
finitely many nonzero perpendicular spaces. If such a space is zero, the
compression inequality already gives `-Y>=0`. Thus `X_a=t K_a` satisfies
every dual slack and has zero trace pairing with `A_a`. This proves
alternative 2 when the resolution fails. The weak dual inequality makes
the two alternatives mutually exclusive. No assertion of generic SDP
strong duality or of rationality of an arbitrary separating witness is
needed.

## 3. A resolution and local spectral bounds give a uniform cost

**Theorem 3.** Suppose a family supplies (Resolution), a uniform `delta>0`
such that `A_a>=delta P_a` on every instance, and neighborhood occurrence
at most a uniform `R`. Then its unrestricted exact rounder cost is at most

```text
C = R/delta.
```

**Proof.** The sufficiency proof of Theorem 1 gives `F_a<=A_a/delta`.
Sum these inequalities and count occurrences. The expected fault-set size
is at most `(R/delta) sum_b Tr(h_b rho)` for every input `rho`. The same
joint effects are supported only on feasible labels, so recovery is exact.

**Finite term collection corollary.** A uniform local spectral bound follows
if the local dimension `q`, term locality `k`, and neighborhood cardinality
`L` are bounded constants, and every term is drawn from one fixed finite
collection of positive local matrices, with no varying scalar weights.
Each neighborhood uses at most `kL` sites. After relabeling those sites and
padding with identities, only finitely many matrices `A_a` can occur:
there are finitely many term choices and finitely many incidence patterns
on at most `kL` sites. The minimum of their nonzero positive eigenvalues is
positive. Tensoring by identities on spectator sites does not change that
minimum. Zero neighborhood matrices impose `F_a=0` and cause no exception.
If every possible neighborhood matrix is zero, any fixed `delta>0` works.

A fixed finite collection of **term matrices** is stronger than constant
local Hilbert-space dimension. General qubit terms can still have
instance-dependent angles or weights. In the paired-projector family,
`Q_N` varies with `N` and `lambda_min(P+Q_N)=2/(N^2+1)`. That family
therefore does not satisfy this finite-collection hypothesis.

The theorem gives a sufficient mathematical route to the NO-side energy
floor. The recovery and measurement need not be efficiently implementable
for the bare rounder transfer theorem, but the Hamiltonian reduction
itself must still be polynomial time. This does not discharge the stronger
physical port claim or the YES-side bound.

## 4. Why spanning the subspaces is insufficient

For the pair `P,Q_N`, `N>1`, use singleton energy neighborhoods. The
feasible labels are the three nonempty sets. Their input support subspaces
are `ran P`, `ran Q_N`, and `{0}`. The first two span the entire qubit
space, but no positive weights on their rank-one projectors sum to `I`.
The zero-denominator certificate in the preceding primal/dual artifact
already proves this failure.

Here is an explicit failed normalization attempt. Let `d=N^2+1`,
`G=gg^*` for `g=(N,-1)^T/sqrt(d)`, and `J=I-G`. With `K=P+Q_N`,

```text
K^(-1/2) = sqrt(d/2) (G+J/N).
```

The usual normalization `E_P=K^(-1/2) P K^(-1/2)` and its `Q_N` analogue
does give a POVM summing to `I`. However,

```text
E_P = [[(N-1)^2, -(N^2-1)], [-(N^2-1), (N+1)^2]]/(2d).
```

Its expectation on the kernel vector `(1,0)^T` of `P` is
`(N-1)^2/(2d)>0`. Thus it violates the necessary input support condition
and cannot satisfy `E_P<=C_0 P` for any finite `C_0`. Normalization rotated
the allowed subspaces.

**A sufficient normalization condition.** Suppose positive `T_S` supported
on `V_S` have an invertible sum `M`, and `M` commutes with each projection
onto `V_S`. Then `E_S=M^(-1/2)T_S M^(-1/2)` retains the required supports
and sums to `I`. Functional calculus makes `M^(-1/2)` preserve each
`V_S`, proving the claim. This is an explicit constructive method when
the additional commutation hypothesis is available; mere invertibility
of `M` is insufficient, as the pair shows.

**A noncommuting positive family.** Fix `N=2` and take any number `r` of
disjoint copies of this same pair. Use both terms of each pair as the
neighborhood for each of its two flags. Choose exactly one flag per pair,
independently and uniformly, giving `2^r` joint effects `2^(-r) I`.
Every occurring label is feasible: in each pair prepare `I-Q_2` when `P`
is flagged and `I-P` when `Q_2` is flagged, then take the tensor product.
Every input range is the whole space since `P+Q_2` is positive definite.
Each marginal is `I/2 <= (5/4)(P+Q_2)` on its site, so occurrence two gives
the uniform cost `5/2`, independent of `r`. This explicitly works with one
fixed finite term collection and noncommuting terms. These disjoint pairs
are not a QMA-hard reduction; the example verifies the constructive side
of the criterion, not the conjecture.

**Why constant ancillary randomness is limited.** For input-independent
flags a nonzero marginal is `p_a I` with `p_a>0`. Its required support can
lie in `ran A_a` only if `A_a` is invertible. In particular, on a frustrated
instance whose every neighborhood sum is singular, input-independent
flags would all have to vanish, producing the infeasible empty label.
Such instances require a genuinely input-dependent measurement for this
route; the disjoint-pair construction cannot simply be reused there.

## 5. The remaining construction

The alternative route `rounder-from-uniform-kernel-resolution` asks for
these resolutions on the NO outputs of the same proposed amplifier, with
uniform local spectral bounds and bounded occurrence. It can avoid a
separate bounded-horizon measurement implementation because the bare
rounder theorem is existential. It still needs the resolutions themselves,
a constant combinatorial gap, and a polynomial-time amplifier preserving
the constant locality, dimension, and YES margin. None is supplied by cone
separation or generic normalization. The QPCP root remains OPEN.

The replay script checks exact positive and negative certificates for the
orthogonal and nonorthogonal pair cases, the normalization support failure,
and a zero-energy boundary. These finite cases do not exhaust possible
amplifiers or prove a QMA-hardness reduction.
