# Independent iid pins still break pure-Choi complement duality

Date: 2026-09-12. This note tests the quantum-entropy argument proposed for
Gottschalk's conjecture. It proves an exact counterexample to its proposed
infinite-conditioning duality, including independent iid whole-site pins.
The cellular automaton used here is reversible, and its Choi state is pure,
has full local quantum recovery, and has product-trace marginals on both
sides. It is not a counterexample to surjunctivity.

The operator-algebras agent independently derived and audited the branch
recursion, the CSS correspondence, and all rational bounds. No numerical
computation or exhaustion was used. This is a proof-search note; it does
not change the status of the universal Gottschalk claim.

## 1. The reversible CA and its pure Choi state

Let `H=F_15`, with free generators `s_1,...,s_15`, and put
`G=H x C2`. Write `t` for the nontrivial central element of `C2`. On
binary configurations define

```
K = I + sum_(j=1)^15 R_(s_j),
L = R_t K,
J(a,b) = (a,b+La).
```

All additions are over `F_2`. There are two bits, hence alphabet size
four, per site. The map `J` is a finite-memory involution.

At each site take two reference qubits `R_g` and two output qubits `B_g`.
Start with the product of EPR pairs between matching qubits, and apply
the output controlled-NOT circuit for `J`. Every gate has a first-track
output control and a second-track output target. These gates commute,
have bounded overlap, and can also be colored into finitely many
disjoint-gate layers. Thus they define a quasilocal automorphism and
produce a pure translation-invariant Choi state. The same circuit is
its local quantum decoder.

Both reference and output marginals are the product trace. The finite
CSS stabilizers are exactly

```
X_R(p) X_B(Jp),
Z_R(J^T q) Z_B(q),
```

for finitely supported pairs `p=(a,b)`, `q=(c,d)`, with
`J^T(c,d)=(c+L^T d,d)`. Completeness follows by applying the inverse
Clifford circuit to any finite Pauli operator and using the product
EPR stabilizers.

## 2. Independent whole-site pinning

Fix the root `e` and let `A=R_e`, a two-qubit system. Independently:

* put each reference site other than `e` into a set `S` with probability
  `1/2`;
* put each output site into a set `T` with probability `1/2`.

Define complementary conditioners

```
U = R_S union B_T,
V = R_(G minus (S union {e})) union B_(G minus T).
```

Every pin includes both qubits at its site. The reference and output
coins are independent. For either infinite conditioner, define

```
S(A|U) = inf_(W finite subset U) [S(AW)-S(W)],
```

with entropy in bits. This is the decreasing finite-conditioner limit.
It is bounded between `-2` and `2`.

We prove

```
E[S(A|U)+S(A|V)] > 11/32,
E S(A|U) = E S(A|V) > 11/64.                         (1)
```

In particular complement duality fails even after averaging independent
iid masks at the symmetric pin densities. It would incorrectly predict
that these expectations vanish.

## 3. Root stabilizer ranks and their nonnegative deficits

For finite qubit sets `W`, let `r(W)` be the rank over `F_2` of the
supported stabilizer group. The reduced state is a normalized projection
of rank `2^(|W|-r(W))`, whence `S(W)=|W|-r(W)`.

For an infinite conditioner `U`, let `V_X(U)` be the subspace of the
two root X coordinates obtained from finite X stabilizers supported in
`A union U`; define `V_Z(U)` similarly. Their kernels under restriction
to `A` are exactly the stabilizers supported entirely in `U`. Since
the root space is finite dimensional, increasing finite conditioners
attain the limiting dimensions. Therefore

```
S(A|U) = 2-dim V_X(U)-dim V_Z(U).                    (2)
```

Finite-support pairing gives

```
V_X(U) perpendicular V_Z(V),
V_Z(U) perpendicular V_X(V).                        (3)
```

For example, for the first pairing, reference supports of `p` and
`J^T q` meet only at the root, while output supports of `Jp` and `q`
are disjoint. Thus

```
<p(e),(J^T q)(e)> = <p,J^T q> = <Jp,q> = 0.
```

Consequently each of

```
2-dim V_X(U)-dim V_Z(V),
2-dim V_Z(U)-dim V_X(V)
```

is nonnegative, and their sum is `S(A|U)+S(A|V)`.

## 4. One rank deficit is an exact finite-witness problem

Condition on the event `e in T`, of probability `1/2`.

An X stabilizer supported in `A union U` must have

```
supp(a) subset (S intersect T) union {e},
La = 0 on (G minus (S union T union {e})).
```

These are the only restrictions on `a`: the second track `b` can cancel
`La` wherever a reference pin is available but the output pin is not.
The root coordinate `b(e)` is free because the root output is pinned.
Let `E_ker` be the event that a finite-support admissible `a` exists with
`a(e)=1`. Then

```
dim V_X(U) = 1 + 1_(E_ker).                          (4)
```

For a Z stabilizer supported in `A union V`, the second component `d`
must be supported on sites outside both `S` and `T`, and `L^T d` must
vanish on `S intersect T`, except that a nonzero root coordinate is
allowed. The first component `c` cancels the remaining coordinates
wherever the output pins permit. Since `e in T`, both `c(e)` and `d(e)`
are zero; the sole possible root Z coordinate is `(L^T d)(e)` on the
first track. Let `E_span` denote existence of such a finite-support
`d` with `(L^T d)(e)=1`. Then

```
dim V_Z(V) = 1_(E_span).                             (5)
```

The two events are disjoint: pairing a kernel witness with a span
witness would give `0=1`. Equations (4)-(5) show that this pair's rank
deficit is exactly

```
1-1_(E_ker)-1_(E_span).                              (6)
```

## 5. The relevant Tanner component is a regular tree

The matrix of `K` has variable/check incidence edges labeled
`1,s_1,...,s_15`. Its bipartite graph is the universal cover of the
graph with two vertices and sixteen parallel edges: its fundamental
group is freely generated by the fifteen edge differences. Hence it
is the sixteen-regular tree.

The factor `R_t` separates each component's variable sites and check
sites into different `C2` layers. Thus they correspond to disjoint
physical sites. Away from the forced root:

* a variable is available when its site lies in `S intersect T`, with
  probability `1/4`;
* a check is imposed when its site lies outside both `S` and `T`, also
  with probability `1/4`.

All these variable and check choices in this component are independent.
The other Tanner component cannot change either root event.

## 6. Finite parity witnesses obey a least-fixed-point recursion

For a directed variable-to-check branch, call the variable good if it
is available and can be assigned value one in a finitely supported
assignment in its branch that satisfies every imposed check in that
branch. The parent check is omitted.

The exact criterion is: the variable is available, and each of its
fifteen child checks is either absent or has at least one good child
variable. Necessity follows because an imposed check receiving a one
from its parent must have a nonzero child. In a finite witness, such
a child supplies a finite witness in its disjoint subtree. Conversely,
choose one good child at each imposed check and combine its finite
witnesses. There are finitely many children, so this union is finite.

Let `p_n` be the probability of a witness with bounded branch depth,
starting with `p_0=0`. Independence of the tree subbranches gives

```
p_(n+1) = f(p_n),
f(x) = (1/4) [1-(1/4)(1-x)^15]^15.
```

Every finite witness has finite depth. Therefore `p=lim p_n` is the
least fixed point of `f`, and it is exactly the finite-witness
probability. No assertion about infinite-support witnesses is used.

The dual check-to-variable witness problem has the same recursion:
interchanging the two kinds of vertices leaves both availability
probabilities equal to `1/4`.

The forced root variable has a finite kernel witness exactly when each
of its sixteen adjacent checks is absent or has a good continuation.
It lies in the finite check span exactly when at least one adjacent
check has a finite dual continuation. Thus

```
P(E_ker | e in T) = [1-(1/4)(1-p)^15]^16,
P(E_span | e in T) = 1-(1-p)^16.                     (7)
```

For the second equivalence, necessity follows by restricting a finite
dual witness to a selected root-adjacent check's subtree. Sufficiency
uses one good branch, leaving the root as its only uncancelled
variable boundary. Multiple branches cannot produce a witness when
none of the individual branches is good, since their subtrees are
disjoint. Parity at the root requires an odd number, so one is enough.

## 7. Exact rational lower bound

Set `delta=1/64`. Bernoulli's inequality gives

```
(1-delta)^15 >= 49/64,
1-(1/4)(1-delta)^15 <= 207/256 < 13/16.
```

Moreover

```
(13/16)^5 < 3/8,
```

because `371293 < 393216`. Hence

```
f(delta) < (1/4)(13/16)^15 < 27/2048 < 1/64.
```

Since `f` is increasing, iteration from zero stays below `delta` and
`p<=1/64`. Therefore

```
(1-p)^16 >= 1-16p >= 3/4,
[1-(1/4)(1-p)^15]^16 < (13/16)^16 < 1/16.
```

The final bound uses `(13/16)^4<1/2`, equivalently
`28561<32768`. By disjointness and (7),

```
P(neither E_ker nor E_span | e in T) > 11/16.        (8)
```

The deficit in (6) is nonnegative and equals one on this event.
The other paired deficit in (3) is always nonnegative. Multiplying
by `P(e in T)=1/2` proves the first inequality in (1).

Complementing all pin coins exchanges `U` and `V` and preserves their
joint law. Their expected conditional entropies are therefore equal,
which proves the second inequality in (1).

## 8. Consequence for the active proof attempt

At symmetric independent pin densities, the proposed identity

```
F(t,u) = -F(1-t,1-u)
```

would force `F(1/2,1/2)=0`. Here it is strictly greater than `11/64`
bits. The failure occurs for an actual reversible CA on a sofic
group, with a pure Choi state and local full quantum recovery.

This excludes using global purity to cancel the missing infinite-pin
entropy contributions in the proposed surjunctivity proof. It does
not exclude a different integrated inequality that explicitly counts
those contributions. No such inequality is established here, and
Gottschalk's conjecture remains unresolved by this computation.
