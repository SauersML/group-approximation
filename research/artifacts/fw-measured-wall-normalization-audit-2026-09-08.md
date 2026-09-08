# FW does not supply the measured-wall step in the lamp strategy

2026-09-08. This audit excludes two generic inferences: replacing cardinal
displacements by measured displacements in the distorted-cyclic argument,
and recovering a fixed integer scale from matrix norm estimates. It does
not rule out a different use of FW with additional lamp structure.

## 1. A concrete FW group with an unbounded measured-wall length

Let `G=SL_2(Z[sqrt(2)])`. Cornulier proves that this group has FW in
**Example 6.A.8**, using distortion of the upper and lower unipotent
subgroups and bounded generation. The relevant discrete input is
**Corollary 6.A.2**: every cardinal-definite function on a cyclic group
has the form `m|n|+b(n)`, with `m` a nonnegative integer and `b` bounded.
Hence sublinear cardinal displacement is bounded. See
[Cornulier's primary text](https://www.normalesup.org/~cornulier/fw.pdf),
pp. 42--44, also Corollary 6.A.4.

Let `sigma_+,sigma_-` be the two real embeddings. The diagonal action
on `H^2 x H^2` has the measured-wall length

```text
ell(g)=d_H(i,sigma_+(g)i)+d_H(i,sigma_-(g)i).
```

Each summand is a wall distance by the invariant Crofton measure on
hyperbolic half-spaces, normalized to give hyperbolic distance; use the
disjoint union of the two wall spaces. This construction is recorded in
[Chatterji--Drutu--Haglund, Example 3.7](https://chatterj.perso.math.cnrs.fr/papers/CDHMedian.pdf),
p. 900. On the standard Borel space of oriented half-spaces, if `A` is
the set of half-spaces containing the base point, it gives
`ell(g)=mu(A triangle gA)` for an invariant sigma-finite measure.

For `u=[[1,1],[0,1]]`, the upper half-plane distance formula gives

```text
ell(u^n)=4 asinh(|n|/2).
```

This is unbounded and sublinear in `|n|`, although `<u>` is distorted
in the FW group above. Thus the discrete cyclic inference used in the
bounded-generation proof is false for measured-wall lengths. Its
conclusion cannot be imported after dropping the cardinal hypothesis.

## 2. The failure also occurs for bounded binary lamp displacements

The fact that normalized matrix distances are bounded does not repair
the inference. Here is an explicit bounded version of the preceding
example.

For `t>0`, take Poisson configurations `omega` on the measured
half-space space with intensity `t mu`, and add an independent uniform
bit `epsilon`. Define

```text
beta(g,omega)=#(omega intersect (g^(-1)A triangle A)) modulo 2,
g.(omega,epsilon)=(g omega,epsilon+beta(g,omega)).
```

Every count is finite almost surely. The identity

```text
beta(gh,omega)=beta(g,h omega)+beta(h,omega) modulo 2
```

follows by symmetric-difference cancellation. Since `G` is countable,
all these statements hold on one invariant conull set. The action
preserves the product probability measure `nu_t`.

For `E={epsilon=0}`, the Poisson parity formula yields

```text
nu_t(E triangle gE)=(1-exp(-2t ell(g)))/2.
```

Consequently, for every fixed finite generating set `S`,

```text
max_(s in S) nu_t(E triangle sE) -> 0       as t -> 0,
sup_(g in G) nu_t(E triangle gE)=1/2        for every t>0.
```

Thus FW alone does not turn small generator displacement into uniformly
small orbit displacement for probability-measured cuts. The variables
`1-2 1_(gE)` are commuting binary-valued lamps with exact covariance;
the example is not merely an arbitrary real metric. No finite-matrix
approximation of this probability action is claimed, and it has not
been shown to satisfy the extra relations of a proposed Clifford group.

## 3. The exact loss of the integer scale in matrix models

For commuting diagonal projections `P_A,P_B in M_d`,

```text
rank(P_A-P_B)=|A triangle B|,
||P_A-P_B||_(2,d)^2=|A triangle B|/d.
```

The normalized mesh is `1/d`, so no positive atom size survives as
`d` grows. Taking `d=n^2` and `|A triangle B|=n` gives vanishing
normalized displacement and diverging absolute cardinal displacement.

Nor does operator-norm convergence bound absolute rank. Let `P_0` be
the projection onto `(1,0)` and `P_theta` the projection onto
`(cos(theta),sin(theta))`. For `0<theta<pi/2`,

```text
||P_theta-P_0||=sin(theta),
rank(P_theta-P_0)=2.
```

Their direct sum over `m` identical blocks has the same operator norm,
absolute rank `2m`, and normalized squared Hilbert--Schmidt norm
`sin(theta)^2`. Thus `theta->0` and `m->infinity` give norm-close
conjugate projections with unbounded full rank of their difference.
The corresponding exact involutions `I-2P_theta` have the same
phenomenon. These pairs need not commute; the example addresses the
conjugation/rounding step, not simultaneous diagonalization.

Keeping unnormalized rank therefore does not by itself produce a
finite-valued cardinal-definite limit. Rank is also discontinuous in
operator norm, as this example shows.

## 4. What additional discrete hypothesis would help

There is a valid elementary extension of FW: suppose an actual
measure-preserving action is given on a discrete set, every point has
finite weight at least `a>0`, and
`mu(A triangle gA)<infinity` for every `g`. Then the symmetric
differences are finite sets. FW supplies an invariant set `B` with
`D=A triangle B` finite, and

```text
mu(A triangle gA)<=2 mu(D)       for every g.
```

Normalized matrix counting measures have no dimension-independent
lower bound `a`. Uniform bounds on absolute rank displacement could
be useful additional input, but a route would still have to construct
an exact compatible action on a discrete set and identify its
displacements with those ranks. Neither such a construction nor the
required rank bounds follow from the estimates above.

The precise surviving task is to exploit extra lamp relations to
obtain this missing discrete structure, or another rigidity argument
that applies to the actual matrix models. FW and bounded generation
by distorted cyclic subgroups alone do not provide the generic
measured-wall inference tested here.

The Poisson cocycle, cyclic distance formula, and rank calculations
were independently audited as symbolic arguments. No local computation,
formal proof checker, or finite-matrix realization was used.
