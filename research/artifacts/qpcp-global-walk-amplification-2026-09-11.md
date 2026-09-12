# Positive transfer operators give global tensor amplification

Date checked: 2026-09-11. This is a finite-dimensional proof, with a small
exact replay. No large computation is involved.

The result below supplies an affirmative alternative to the layer-restricted
amplifier in the existing Dinur-iteration audit. An expander walk over **all**
clauses gives a ground-energy gain linear in its length, with a constant
saturation threshold. It needs no commuting-layer decomposition. Consequently
a locality reduction with loss sublinear in the walk length would suffice
for quantum PCP. The locality reduction is still open.

Operator amplification along expander walks is prior art. In particular,
Jeronimo--Mittal--Roy--Wigderson (JMRW), arXiv:2209.07024v2, Theorem 3.6,
already implies the qualitative linear gain by the cyclic-shift construction
in Section 6 below. The positivity argument here gives an explicit stronger
bound for this special case. No originality or priority claim is made for
the amplification technique or for the streaming consequence.

## 1. Statement

Let `K` be a nonzero finite-dimensional Hilbert space and let

```text
H = (1/m) sum_(v=1)^m h_v,   0 <= h_v <= I,   epsilon=lambda_min(H).
```

Let `M` be the transition matrix of an undirected regular multigraph on
`[m]`, with nonnegative entries, uniform stationary measure and

```text
u = (1,...,1)/sqrt(m),   P_0=|u><u|,   ||M-P_0|| <= lambda < 1.
```

For `t>=2`, take a stationary walk with **t vertices**, hence `t-1` edges,
and put

```text
Q_v = I-h_v,
A_t = E_(v_1,...,v_t) tensor_(j=1)^t Q_(v_j),
G_t(H) = I-A_t.                                                    (GW1)
```

All factors in a summand act on distinct tensor copies of `K`. They need
not commute as operators on the original `K`.

**Theorem.** The following bounds hold:

```text
1-(1-epsilon)[1-(1-lambda^2)epsilon]^((t-2)/2)
   <= lambda_min(G_t(H)) <= min{1,t epsilon}.                      (GW2)
```

For `lambda<=1/2` and even `t>=2`, a convenient rational consequence is

```text
lambda_min(G_t(H)) >= min{ (3t+2)epsilon/16, 1/2 }.                 (GW3)
```

The lower bound concerns all states, including arbitrary entanglement
between copies. For `k`-local qudit terms, the new terms have locality at
most `tk`, the local dimension is unchanged, and there are exactly
`m d^(t-1)` terms counted with edge multiplicity in a `d`-regular graph.
They are positive contractions; if the input terms are projections, so
are the output terms.

## 2. The transfer-operator proof

Work on `L=C^m tensor K^(tensor t)` and define

```text
U: K^(tensor t) -> L,       U psi = u tensor psi,
P = UU*,                    T = M tensor I,
D_j = sum_v |v><v| tensor Q_v^(j).
```

Here `Q_v^(j)` acts on copy `j` and is identity on every other copy.
Every `D_j` is a positive contraction. Expanding the vertex indices gives
the exact identity

```text
A_t = U* D_1 T D_2 T ... T D_t U.                                (GW4)
```

The factor `1/m` from the two copies of `u` is precisely the stationary
starting probability. Each entry `M_(v_j,v_(j+1))` is the corresponding
transition probability. This is a matrix identity, without a product-state
assumption.

Since `Q_v^2<=Q_v`,

```text
U* D_j^2 U = (1/m) sum_v (Q_v^2)^(j)
           <= (I-H)^(j) <= (1-epsilon)I.
```

It follows that

```text
||D_j U||^2 <= 1-epsilon,
||D_j P D_j|| = ||D_j U||^2 <= 1-epsilon.                         (GW5)
```

The two-sided expander assumption gives

```text
T^2 <= lambda^2 I + (1-lambda^2)P.
```

Congruence by `D_j` and (GW5) imply

```text
D_j T^2 D_j
 <= lambda^2 D_j^2+(1-lambda^2)D_j P D_j
 <= [1-(1-lambda^2)epsilon] I.
```

Consequently, with `r=sqrt(1-(1-lambda^2)epsilon)`,

```text
||D_j T|| = ||T D_j|| <= r.                                      (GW6)
```

Group (GW4), keeping the two endpoint factors:

```text
A_t = (U*D_1) T (D_2 T) ... (D_(t-1) T) (D_t U).
```

There are `t-2` middle factors of the form `D_j T`. The two endpoints
each have norm at most `sqrt(1-epsilon)`, and `||T||=1`. Thus

```text
||A_t|| <= (1-epsilon) r^(t-2).                                  (GW7)
```

Each summand of `A_t` is a positive contraction, so
`lambda_min(I-A_t)=1-||A_t||`. This proves the lower bound in (GW2).
The zero- and unit-energy endpoints are included: when `epsilon=1`,
(GW5) makes every endpoint zero.

For completeness, take a normalized ground vector `psi` of `H` and use
`psi^(tensor t)`. For each walk, the scalar union bound gives

```text
1-product_j (1-<psi,h_(v_j) psi>)
 <= sum_j <psi,h_(v_j) psi>.
```

Every walk coordinate is uniform, so averaging gives at most `t epsilon`.
This proves the upper bound. No normalization factor is discarded.

## 3. Rational linear gain

Write `t=2s+2`, `s>=0`, and `B=1+3s/4=(3t+2)/8`. For `0<=x<1`,

```text
(1-x)(1-3x/4)^s <= 1/[(1+x)(1+3s x/4)] <= 1/(1+B x).
```

The first inequality follows from `1-x<=1/(1+x)` and
`(1-y)^s<=1/(1+s y)`; the latter follows by differentiation of
`(1-y)^s(1+s y)` or by Bernoulli's inequality. The case `x=1`
follows directly. Hence (GW2) implies

```text
lambda_min(G_t(H)) >= B epsilon/(1+B epsilon)
                         >= min{B epsilon/2,1/2},
```

which is (GW3). In particular, `t=10` gives
`lambda_min(G_10(H))>=min{2 epsilon,1/2}`.

## 4. Iteration and representation

Constant-degree two-sided expanders with a fixed spectral bound below one
are explicit; taking a fixed graph power gives the bound `1/2` used here.
If needed, repeat every input term the same fixed number of times before
building the graph. This changes no Hamiltonian and costs a constant
factor in the term count. BMVZ Lemma 2.9 states the all-sufficiently-large-
sizes version needed for this convention.

For any fixed even `t>=10`, iteration of `G_t` has a constant factor
increase in sites and term count at every round. With `t=10`, a NO energy
at least `1/q(n)` reaches `1/2` in `O(log q(n))` rounds, while an initially
exponentially small YES energy is multiplied by at most `10` per round.
The number of sites, terms, and tensor leaves is polynomial for
`O(log n)` rounds.

One must describe the terms by their tensor leaves during this iteration,
not write their exponentially large dense matrices. Indeed a new accepting
factor is a tensor product of old accepting factors. Flattening the nested
products gives tensor products of the original constant-locality accepting
factors on disjoint original-size copies. This is an explicit polynomial
description and supports streaming measurement. Its locality is growing,
so this consequence does not establish quantum PCP.

## 5. What composition now suffices

Fix a constant `k_0>=5` and a fixed even `t`. Suppose a polynomial-time
reducer takes `G_t(H)` for every normalized `k_0`-local qubit Hamiltonian
`H` and returns a normalized `k_0`-local qubit Hamiltonian `R_t(G_t(H))`
such that, for constants `L>=1` and `A,S>0`,

```text
lambda_min(R_t(G_t(H))) >= lambda_min(G_t(H))/L,
lambda_min(R_t(G_t(H))) <= A lambda_min(G_t(H))+2^(-n),             (RED-G)
n <= number of output qubits <= S n,
number of output terms <= S m.
```

The constant `S` may absorb the walk's fixed term-count factor. Descriptions
also obey the following **linear growth bound**: if `B` is the maximum
bit length of an input term description, the maximum output term-description
length is at most `S(B+n+m)`. The bound includes tensor-support labels and
entries. The lower site bound can be enforced by
padding with qubits on which every term acts as identity. Assume

```text
L < (3t+2)/16.                                                   (NET)
```

Then this reducer and (GW3) imply quantum PCP. Put
`g=(3t+2)/(16L)>1` and `b=1/(2L)`. The NO recurrence is

```text
epsilon_(i+1) >= min{g epsilon_i,b}.
```

Use the exponentially complete, inverse-polynomial-sound 5-local hardness
seed recorded in `bmvz-iterable-tensor-gap-amplification`, padding to at
least the input length `n` if needed. After `O(log n)` rounds the NO energy
is at least `b`. The YES recurrence is

```text
a_(i+1) <= At a_i+2^(-n_i) <= At a_i+2^(-n).
```

Thus after `ell=O(log n)` rounds,

```text
a_ell <= max{1,At}^ell [a_0+ell 2^(-n)] = negligible(n).
```

Sites, term count and maximum description length obey a fixed linear
recurrence in `(n_i,m_i,B_i)`, so all three stay polynomial through
`O(log n)` rounds. Each round is polynomial time in its current description,
which also makes the complete computation polynomial time. Merely assuming
polynomial bit growth in one call would not suffice: squaring the current
bit length at each of `O(log n)` rounds can be superpolynomial.
The output has fixed locality `k_0`, qubits, normalized terms and constant
promise gap. This is the required root statement.

In particular, a family of reducers with loss `L_t=o(t)` satisfies (NET)
for some fixed even `t`. No uniform constant lower bound on `1/L_t` is
required. The hard construction obligation is exactly the reducer; this
artifact does not supply it.

## 6. Prior art and source boundary

The primary sources checked on 2026-09-11 are:

1. [BMVZ, arXiv:2510.01333v1](https://arxiv.org/html/2510.01333v1),
   especially Definitions 1.6 and 1.9, Theorem 1.2, Lemma 2.9, Section 7,
   Section 8 and Appendix A. Their construction chooses one commuting
   layer and walks only among its clauses. Here the graph is on the whole
   clause list. The positive proof is unavailable layer by layer if each
   individual layer has zero ground energy. This result does not prove
   a stronger bound for their particular layer-restricted construction.

2. [JMRW, arXiv:2209.07024v2](https://arxiv.org/html/2209.07024v2),
   Section 3, particularly Lemma 3.5 and Theorem 3.6. For general
   contraction-valued emissions with average norm `alpha`, their bound
   is `[1-(1-lambda)^2(1-alpha)]^floor(ell/2)` for a walk of `ell`
   edges. To apply it here, let `C` cyclically permute the `t` copies and
   use the single emission `f(v)=Q_v^(1) C`. Its mean has norm
   `1-epsilon`; a product of `t` emissions is, after the identity `C^t=I`,
   a tensor product with one factor in each copy. The walk reversal and
   copy permutation do not affect the norm. This recovers qualitative
   linear amplification as a prior-art corollary. (GW2) sharpens the
   constants using positivity and keeps both endpoints explicitly.

3. [Jeronimo--Mittal--Roy, RANDOM 2025](https://drops.dagstuhl.de/storage/00lipics/lipics-vol353-approx-random2025/html/LIPIcs.APPROX-RANDOM.2025.49/LIPIcs.APPROX-RANDOM.2025.49.html),
   Section 3 and the associated full-version link. This is relevant
   tensor-valued expander-walk prior art, so tensor-valued sampling itself
   is not asserted new here.

4. [Bafna--Vyas, ECCC TR26-150](https://eccc.weizmann.ac.il/report/2026/150/)
   still identifies quantum PCP as open. Nothing above changes that status.

The inspected primary full texts did not supply a reducer satisfying
(RED-G)/(NET). Their available code/data links did not identify an
implementation of such a reducer. These bounded searches are not an
exhaustive novelty certification. The graph imports a proved reusable
inequality and a conditional implication, not a claim of a newly solved
external conjecture.

## 7. Exact finite replay

`check-qpcp-global-walk-2026-09-11.py` checks a four-copy noncommuting
qubit example with rational arithmetic. It checks the complete walk sum,
the transfer identity, the normalization, the projector identities and
an exact LDL certificate for the promised spectral lower bound. It is
a regression certificate for the displayed finite example; the universal
theorem is the proof in Sections 1--3.

Replay completed locally in 1.43 seconds, with standard-library rational
arithmetic only. The two input projectors have ground energy `1/5`;
all `128` labelled four-vertex walks are included. Both the transfer
identity and the bound `lambda_min(G_4(H))>=8/25` have exact certificates
in `qpcp-global-walk-replay-2026-09-11.json`.
