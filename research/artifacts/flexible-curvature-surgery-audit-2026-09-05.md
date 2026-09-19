# Flexible curvature surgery: exact supports and an orthogonal rank ledger

This audit allows generator changes tending to zero and deletion or trivial
replacement of `o(d)` dimensions. It does **not** require the surgery to
cost `O(delta)` at the original defect scale. The earlier cyclic-shift
halo example only disproved that stronger scale requirement; it does not
disprove flexible correction.

The affirmative result below shows precisely how exact support surgery
would complete a stability proof. Its cumulative cost is governed by the
**sum of deleted relative ranks**, not the sum of their square roots.
That distinction makes some slow defect-scale resets viable. The known
curvature concentration theorem supplies neither exact reducing supports
nor the uniform cumulative rank bound required here.

## 1. An exact support surgery really decreases the defect

Use normalized trace on `M_d`. Let `W_s` be unitary generator matrices,
and let `P` be a projection commuting **exactly** with every `W_s`.
Write `Q=I-P`. Define

```text
U'_s=W_s Q+P.
```

These matrices are unitary: both summands are supported on reducing
subspaces. On `P C^d` they form the trivial representation. For every word
`w`,

```text
U'(w)=W(w)Q+P,
U'(w)-I=(W(w)-I)Q,
||U'_s-W_s||_2<=2 sqrt(tr(P)).                           (FCS1)
```

Thus if all defining relators have operator norm at most epsilon on `Q`,
the new HS defining defect is at most epsilon. If `tr(P)->0`, the
generator correction tends to zero, regardless of whether it is larger
than the preceding defining defect. One can equivalently delete `P` and
then add back its dimension as a trivial summand; no growth in dimension
is necessary.

The commutation assumption cannot be replaced silently by small
normalized-HS commutators. With only almost invariance, `W_s Q+P` is
not unitary, and taking polar parts introduces new word errors. Those
errors are small in an absolute norm but need not decrease the previous
defect or satisfy a summable budget.

## 2. Orthogonal supports give a better iteration budget

Here is a complete deterministic correction lemma for a fixed finite
presentation. Suppose an iteration on `C^d` has generator tuples `U^k`,
intermediate tuples `W^k`, and pairwise orthogonal projections `P_k`.
Let `F_k=sum_(i<k) P_i` be the already repaired block. Assume:

1. Both `U^k_s` and `W^k_s` act as identity on `F_k C^d`, so they do not
   mix the repaired block with its complement.
2. `P_k<=I-F_k` commutes exactly with every `W^k_s`.
3. The next tuple is `U^(k+1)_s=W^k_s(I-P_k)+P_k`.
4. `max_s||W^k_s-U^k_s||_2<=a_k`, `sum_k a_k<infinity`, and
   `sum_k tr(P_k)<=eta`.
5. The defining defects of `U^k` tend to zero.

Then the tuples converge to an exact representation `rho:G->U(d)` and

```text
max_s ||rho(s)-U^0_s||_2 <= sum_k a_k+2 sqrt(eta).        (FCS2)
```

Proof: set

```text
A_(k,s)=W^k_s-U^k_s,
B_(k,s)=U^(k+1)_s-W^k_s=(I-W^k_s)P_k.
```

The `A` series converges absolutely in 2-norm. Since `P_k` reduces `W^k`,
the matrix `B_(k,s)` is supported on `P_k` on **both** sides. Consequently
different `B` terms are orthogonal in matrix 2-space, and

```text
||sum_k B_(k,s)||_2^2=sum_k ||B_(k,s)||_2^2
 <=4 sum_k tr(P_k)<=4 eta.
```

Their series therefore converges as well. Telescoping proves convergence
of `U^k_s` and `(FCS2)`. For fixed `d`, 2-norm convergence is equivalent
to ordinary matrix convergence; the limiting generators are unitary.
Continuity of each finite relator word and assumption 5 make the limit
an exact representation. This proves the lemma.

The lemma also explains a relevant design constraint: later corrections
must preserve each already frozen block. If later steps mix it back into
the active space, the orthogonality estimate is lost. Merely reporting
the rank of each step separately is not a cumulative bound.

Two finiteness details matter. Zero cuts are permitted. For fixed `d`
there can only be finitely many nonzero orthogonal cuts, but smooth
corrections can continue after the last one; exactness follows from
the vanishing-relator hypothesis and convergence, not just exhaustion of
the cuts. For a finite schedule, the estimate gives an exact endpoint
only if the terminal tuple already has zero defining defect.

## 3. A Dini rank modulus is enough for a full correction theorem

Suppose a proposed exact-support repair method has the following uniform
one-step guarantee, including when a previously repaired block is frozen:

```text
input defining defect <= delta;
intermediate generator correction <= C delta;
new reducing support has relative rank <= m(delta);
after trivial replacement, defining defect <= delta/2.  (FCS3)
```

Let `m` be nondecreasing. If

```text
D_m(delta):=sum_(k>=0) m(2^(-k)delta) < infinity,
lim_(delta->0) D_m(delta)=0,                             (FCS4)
```

then every sufficiently accurate input tuple has an exact correction in
the same dimension with

```text
max_s ||rho(s)-U_s||_2
 <= 2 C delta+2 sqrt(D_m(delta)).                        (FCS5)
```

Indeed, iterate `(FCS3)` inside the remaining active block while keeping
the deleted blocks trivial. The cohomological corrections have total
cost at most `2 C delta`; monotonicity bounds the total discarded rank
by `D_m(delta)`. Apply `(FCS2)`. This proves a genuine stability criterion,
not just the existence of a sequence of improving approximate tuples.

This criterion permits costs much larger than the original defect scale.
For example `m(delta)<=C_0 delta^a`, with **any** `a>0`, gives correction
of order `delta+delta^(a/2)`. Even

```text
m(delta)<=C_0/[log(e/delta)]^(1+epsilon), epsilon>0,
```

has `(FCS4)` and gives a correction tending to zero. Summing the naive
per-step distances `2 sqrt(m(delta_k))` would incorrectly demand stronger
decay. Conversely the statement `m(delta)->0` alone does not imply
`(FCS4)`; `m(delta)=1/log(e/delta)` has a divergent dyadic sum.

More generally, a defect-scale reset need not halve the defect at every
step. The exact lemma only needs the final defects to tend to zero,
the smooth corrections to have small summable total, and the deleted
blocks to have small total rank. An adaptive schedule is valid if it
proves those three global facts. Smallness of each fixed step along an
input sequence does not prove them for a growing number of steps.

All the displayed bookkeeping used the original dimension. If a repair
method instead uses the current active dimension, let `q` be the active
fraction. The active defect is `delta/sqrt(q)`. An active smooth
correction bounded by `C delta/sqrt(q)` becomes `C delta` after return
to the original normalization, while the deleted rank bound becomes
`q m(delta/sqrt(q))`. Under `q>=1/2` the latter is bounded by
`m(sqrt(2)delta)`. Consequently
`D_m(sqrt(2)delta)<1/2` supplies a bootstrap: every partial rank sum stays
below one half, so the normalization estimate remains valid at every
stage. The corresponding correction bound is
`2C delta+2 sqrt(D_m(sqrt(2)delta))`. The one-step halving claim here
measures the output, including its newly trivial block, in the same
pre-cut active dimension as the input; only afterwards is that trivial
block removed from the next active space.

## 4. Why existing concentration does not yet supply this method

The established concentration result gives, after an `O(delta_j)`
perturbation and a subsequence,

```text
HS defining defect = O(delta_j),
trace-norm defining defect = o(delta_j),
tr(P_j)->0,
||(V_j(r)-I)(I-P_j)||_op=o(delta_j).
```

It has no invariance conclusion for `P_j`. Its trace bound is expressed
through the produced quantity
`a_j=max_r||V_j(r)-I||_1/delta_j->0`, not through a proved uniform
function of delta with a Dini bound. It also gives a subsequence
improvement, not a finite-dimensional repair operator with `(FCS3)`
available at every subsequent stage.

For each fixed number of stages, one may pass to successive subsequences
and make the sum of the finitely many ranks and distances tend to zero.
That only produces further approximate representations. It does not
justify running enough stages to reach a dimension-dependent Frobenius
threshold, nor an infinite iteration for an individual input matrix.
A growing number of repairs must have its own cumulative estimates.

Thus allowing `o(d)` flexibility removes the earlier demand that every
surgery preserve the initial defect scale, but leaves two concrete
requirements: an exact-compatible support or reconnection, and a global
rank/error ledger such as `(FCS2)`.

## 5. Exact saturation can still consume the entire original dimension

Padding alone does not turn an almost invariant small support into an
exact small reducing support. An explicit example already occurs with
free generators, hence with a group having `H^2(G,H)=0` for every Hilbert
module.

On `C^d`, let `S_d` be the cyclic shift, let `D_d` be the diagonal clock
matrix with distinct d-th roots of unity, and let `P=e_(00)`. The matrices
`S_d,D_d` give an exact representation of the free group `F_2`. They
generate `M_d`: the clock's spectral projections are the coordinate
rank-one projections, and the shift transports them cyclically.
Consequently this representation is irreducible.

The projection satisfies

```text
tr(P)=1/d,
[P,D_d]=0,
||[P,S_d]||_2=sqrt(2/d) -> 0.
```

Yet every invariant subspace containing its range is the whole `C^d`,
since the `S_d` orbit of that range includes every coordinate. The same
remains true after padding the representation by **any** auxiliary exact
representation: a reducing projection whose range contains the original
`P C^d` must contain all of the original `C^d`, because the original
summand is still invariant and its orbit span is unchanged. Its rank is
therefore at least d, even if the padding is `o(d)`.

To make this support carry actual concentrated curvature, use the
presentation `<a,c,b|b=1>`, still a free group of rank two, with

```text
V_a=S_d,  V_c=D_d,
V_b=I+(exp(i d^(-1/2))-1)P.
```

The sole defining defect has HS norm asymptotic to `1/d`, trace norm
asymptotic to `d^(-3/2)`, and support exactly `P`. Exact saturation of
that support under the unchanged `a,c` matrices costs the full original
dimension. The tuple is nevertheless easily correctable by setting
`V_b=I`. This example rules out **unchanged-actor exact saturation**,
including saturation aided only by padding; it does not refute a surgery
that changes the actor matrices by `o(1)`.

For an arithmetic Kazhdan actor the logical distinction is the same.
Even when an actor is already exact, property `(T)` can round a projection
of trace tending to zero to the zero invariant projection. It does not
produce a small invariant projection containing the prescribed curvature
support. Requiring containment is an additional condition, and the
irreducible example shows why it matters.

## Outcome

An exact-support repair with a Dini cumulative rank bound would complete
the desired kind of normalized-HS stability argument, and its allowable
cost is substantially more flexible than defect-scale preservation. The
proof above accounts for both convergence and the total changed fraction
of dimension. The current concentration and halo constructions do not
provide that repair. No exact subgroup holonomy or non-hyperlinear group
is asserted here.

All computations above are exact symbolic matrix identities. No code,
build, numerical job, commit, or branch was used for this audit.
