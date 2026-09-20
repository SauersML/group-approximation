# Constant combinatorial gap and a uniform energy floor do not force compatible local syndrome effects

Swarm attack on `amplifier-has-compatible-local-syndrome-effects`,
2026-09-16. Ordinary mathematical proofs; not a Lean certificate. The
supplementary exact replay is
`experiments/gap-floor-syndrome-separation-2026-09-16/check_separation.py`.

## 0. Scope

The target asks for one tuple `(W,{B_a},{N(a)},C_0,R)` on the NO outputs of
the common amplifier. Its clause 2 is local domination with uniform
constants and its clause 3 is joint fault feasibility. By the 2026-09-11
positive shift audit (`research/artifacts/qpcp-positive-shift-audit-2026-09-11.md`,
sections 3 and 4), clauses 1 to 3 hold trivially on shifted instances, and
the anchored criterion containing this target becomes equivalent to the
root claim once the YES margin is included. So no unconditional proof or
refutation of the target is attempted here.

This artifact proves a separation for **unshifted** instances. Clauses 2 and
3 with uniform constants are not a consequence of any of the following, even
taken together and even when `W,B` are completely unrestricted:

- locality two, qubit sites, norm-one projector terms, maximum degree 512;
- combinatorial gap at least `11/30`;
- normalized ground energy at least `1/30`;
- least bare rounder constant at most `11`.

For every pair of constants `C_0,R` some member of an explicit-up-to-a-graph
family satisfies all of the listed properties and admits no such tuple
(Corollary 7). The mechanism is a necessary local condition, Proposition 3.
The neighborhoods of every frustrated set of terms must jointly contain a
subsystem with a uniformly positive spectral gap. The same family admits no
uniform kernel resolution in the sense of
`amplifier-admits-a-uniform-local-kernel-resolution` either (Remark 8A).

Earlier obstructions cover different ground:

| Node | Gap | Floor | Neighborhoods excluded |
| --- | --- | --- | --- |
| `qubit-pairs-have-half-gap-and-unbounded-rounder-cost` | `1/2` | vanishes | every rounder (cost `(N^2+1)/2`) |
| `nonorthogonal-pair-forbids-single-term-syndrome-ports` | `1/2` | vanishes | singleton neighborhoods |
| primal/dual artifact, pair with both terms | `1/2` | vanishes | that neighborhood, sharp `C_0=(N^2+1)/4` |
| `fixed-term-chain-defeats-bounded-syndrome-neighborhoods` | vanishes | vanishes | bounded size, bounded occurrence |
| this artifact | `11/30` | `1/30` | every system with occurrence `R`, any sizes |

In the first four rows the target's clauses fail together with the bare
rounder bound. Here the bare rounder cost stays below `11`, so the failure
is intrinsic to the local syndrome demand.

## 1. Conventions

`H` is a nonzero finite-dimensional Hilbert space, and `h_1,...,h_m` are
positive operators on it with `0 <= h_a <= I`. For `S subset [m]` put
`K_S = intersection_(a not in S) ker h_a`, with `K_[m] = H`. The set `S` is
**feasible** when `K_S != {0}`. A set `T` of terms is **frustrated** when
`intersection_(a in T) ker h_a = {0}`, that is, when `[m] \ T` is infeasible.
For `U subset [m]` write `H_U = sum_(b in U) h_b` (no normalization).

A **term-flag syndrome tuple** consists of an isometry `W : H -> K` into a
finite-dimensional space, mutually commuting orthogonal projections
`B_1,...,B_m` on `K`, sets `N(a) subset [m]`, and numbers `C_0 >= 0`,
`R >= 1`. Put

```text
Pi_S = product_(a in S) B_a product_(a not in S) (I-B_a),
E_S  = W^* Pi_S W,      F_a = W^* B_a W,      A_a = H_(N(a)).
```

The target's clauses 2 and 3, with every realization requirement of clause 1
dropped, read

```text
(T2)  F_a <= C_0 A_a for every a,   and   #{a : b in N(a)} <= R for every b;
(T3)  E_S = 0 for every infeasible S.
```

A **gadget-flag tuple with a union map** instead has commuting projections
`B_i` indexed by a finite set `I`, neighborhoods `N(i) subset [m]` with every
term in at most `R` of them, and a map `phi` from `I` to subsets of `[m]` with
`|phi(i)| <= M`. The reported term fault set of a gadget outcome `J subset I`
is `phi(J) = union_(i in J) phi(i)`. Its clauses are

```text
(G2)  W^* B_i W <= C_0 H_(N(i)) for every i;
(G3)  W^* Pi_J W = 0 whenever phi(J) is infeasible.
```

The target requires such an explicit map with a constant multiplicity cost
but does not fix its form. Section 5 treats only union maps with
`|phi(i)| <= M`.

The **least rounder constant** `C_min(H)` is that of
`combinatorial-gap-and-rounder-give-energy-gap`. For a frustrated instance it
equals `s*/(m lambda_min(H))`, where `H = (1/m) sum_a h_a` and `s*` is the
least feasible cardinality.

## 2. Local frustration certificates

**Lemma 1 (joint projector identities).** Let `B_i`, `i in I`, be commuting
orthogonal projections on `K` and `W : H -> K` an isometry. The `Pi_J`,
`J subset I`, are pairwise orthogonal projections with `sum_J Pi_J = I` and
`B_i = sum_(J containing i) Pi_J`. Consequently `E_J = W^* Pi_J W >= 0`,
`sum_J E_J = I`, and `W^* B_i W = sum_(J containing i) E_J`.

*Proof.* Products of commuting projections are projections. Expanding
`I = product_i (B_i + (I-B_i))` gives `sum_J Pi_J = I`. For `J != J'` some
`i` lies in exactly one of them, and `Pi_J Pi_J'` contains the factor
`B_i (I-B_i) = 0`. Expanding `B_i = B_i product_(k != i)(B_k + (I-B_k))`
gives the formula for `B_i`. Compress by `W` and use `W^*W = I`. `QED`

**Lemma 2 (covering).** Assume (T3) and let `T` be frustrated. Then

```text
sum_(a in T) F_a >= I.                                           (Cover)
```

*Proof.* If `S` is disjoint from `T`, then `T subset [m] \ S` and
`K_S subset intersection_(a in T) ker h_a = {0}`, so `S` is infeasible and
`E_S = 0` by (T3). By Lemma 1,

```text
sum_(a in T) F_a = sum_S |S intersection T| E_S
                >= sum_(S meets T) E_S = sum_S E_S = I.         QED
```

This is the covering inequality of section 3 of
`research/artifacts/qpcp-paired-projector-obstruction-2026-09-07.md`,
derived here for the joint effects of one syndrome tuple through (T3).

**Proposition 3 (local frustration certificate).** Assume (T2) and (T3), and
let `T` be frustrated. Put `U_T = union_(a in T) N(a)`. Then

```text
I <= C_0 min(|T|,R) H_(U_T).                                     (LFC)
```

In particular `C_0 > 0`, the terms in `U_T` have no common kernel vector,
and `lambda_min(H_(U_T)) >= 1/(C_0 min(|T|,R))`.

*Proof.* By (Cover) and (T2),
`I <= C_0 sum_(a in T) A_a = C_0 sum_b #{a in T : b in N(a)} h_b`. The
coefficient of `h_b` vanishes unless `b in U_T`, and it is at most `|T|` and,
by occurrence, at most `R`. Since each `h_b >= 0`, the sum is at most
`min(|T|,R) H_(U_T)`. If `C_0 = 0` the right side is zero, which is
impossible on a nonzero space. `QED`

For the single pair `P,Q_N` with `N(P) = N(Q) = {P,Q}`, (LFC) gives
`1 <= 2 C_0 (2/(N^2+1))`, that is `C_0 >= (N^2+1)/4`. This recovers the lower
half of the sharp constant in
`research/artifacts/qpcp-syndrome-primal-dual-2026-09-07.md`.

**Proposition 3G (gadget version).** Assume (G2) and (G3), and let `T` be
frustrated. Put `Phi_T = {i in I : phi(i) meets T}` and
`U_T = union_(i in Phi_T) N(i)`. Then `I <= C_0 R H_(U_T)`.

*Proof.* If `E_J != 0`, then `phi(J)` is feasible by (G3). The argument of
Lemma 2 shows that `phi(J)` meets `T`, so some `i in J` has `phi(i)` meeting
`T`, that is, `J` meets `Phi_T`. Lemma 1 then gives
`sum_(i in Phi_T) W^* B_i W = sum_J |J intersection Phi_T| E_J >= I`. By
(G2) the left side is at most `C_0 sum_b #{i in Phi_T : b in N(i)} h_b`, and
each coefficient is at most `R` and vanishes off `U_T`. `QED`

## 3. A bounded-degree high-girth graph with a constant fraction of forced monochromatic edges

For a graph `G = (V,E)` and `x : V -> {0,1}`, let `mono_G(x)` be the number
of edges `uv` with `x_u = x_v`, and `tau(G) = min_x mono_G(x)`.

**Lemma 4.** Put `D = 64` and `Delta = 512`. For every integer `g >= 3` there
is a finite simple graph `G = (V,E)` with the following properties:

- `E` is nonempty;
- every vertex has degree at most `Delta`;
- `G` has no cycle of length at most `g`;
- `tau(G) >= |E|/10`.

This is a standard probabilistic construction in the spirit of Erdos's
high-girth argument; a complete proof follows.

*Proof.* Fix `n >= max(100, 400 D^(g-1))`. Let `G_0` be the random graph on
`[n]` that contains each of the `binom(n,2)` pairs independently with
probability `p = D/n`, which is less than one.

(a) *Forced monochromatic edges.* Fix `x` and let `k = |x^(-1)(1)|`. The
number of vertex pairs with equal colors is

```text
M_x = binom(n,2) - k(n-k) >= n(n-1)/2 - n^2/4 = n(n-2)/4.
```

Then `X_x = mono_(G_0)(x)` is binomial with mean `mu_x = p M_x >= 16(n-2)`.
Put `t = ln 2`. Using `1+y <= e^y`,

```text
E exp(-t X_x) = (1 - p + p e^(-t))^(M_x) <= exp(mu_x (e^(-t) - 1)) = exp(-mu_x/2),
```

and Markov's inequality gives

```text
P(X_x <= mu_x/2) <= exp(t mu_x/2) E exp(-t X_x) = exp(-mu_x (1 - ln 2)/2) <= exp(-mu_x/8),
```

because `(1-ln 2)/2 > 0.15 > 1/8`. Since `8(n-2) <= mu_x/2`,
`P(X_x <= 8(n-2)) <= exp(-2(n-2))`. A union bound over the `2^n` colorings
gives

```text
P(some x has mono_(G_0)(x) <= 8(n-2)) <= 2^n e^(-2(n-2)) = e^4 (2/e^2)^n < 10^(-50).
```

(b) *Edge count.* `|E_0|` is binomial with mean and variance at most
`D(n-1)/2 < Dn/2`. Chebyshev's inequality gives
`P(|E_0| >= Dn) <= (Dn/2)/(Dn/2)^2 = 2/(Dn) <= 1/3200`.

(c) *Short cycles.* For `3 <= k <= g`, the complete graph has
`n(n-1)...(n-k+1)/(2k) <= n^k/(2k)` cycles of length `k`, and each lies in
`G_0` with probability `p^k`. The number `Y` of cycles of length at most `g`
in `G_0` therefore satisfies

```text
E Y <= sum_(k=3)^g D^k/(2k) <= D^(g+1)/(6(D-1)) <= D^g,
```

and Markov's inequality gives `P(Y >= 4 D^g) <= 1/4`.

(d) *High degrees.* Each degree is binomial `Bin(n-1,p)`, so
`P(deg v = k) <= binom(n-1,k) p^k <= D^k/k!`. Put
`Z = sum_v deg(v) 1[deg(v) > Delta]`. Then

```text
E Z <= n sum_(k > Delta) k D^k/k! = n D sum_(j >= Delta) D^j/j!
    <= (8/7) n D D^Delta/Delta! <= (8/7) n D (e D/Delta)^Delta = (8/7) n D (e/8)^512.
```

Here the ratio of consecutive terms is `D/(j+1) <= 1/8` for `j >= Delta`,
and `Delta! >= (Delta/e)^Delta`. By Markov's inequality,
`P(Z >= Dn/100) <= (800/7)(e/8)^512 < 10^(-200)`.

*Selection.* The four failure probabilities sum to less than one, so some
graph `G_0` satisfies all of the following:

1. every `x` has `mono_(G_0)(x) > 8(n-2)`;
2. `|E_0| < Dn`;
3. `Y < 4 D^g`;
4. `Z < Dn/100`.

Fix such a graph. Delete one edge from each cycle of length at most `g`,
which removes at most `Y` edges. Delete every edge incident to a vertex of
`G_0`-degree greater than `Delta`, which removes at most `Z` edges. Call
the result `G = (V,E)`, with `V = [n]`.

- *Degrees.* A vertex of `G_0`-degree above `Delta` has degree zero in `G`.
  Every other vertex keeps degree at most `Delta`.
- *Girth.* A cycle of `G` of length at most `g` is such a cycle of `G_0`, and
  one of its edges was deleted. So no such cycle exists.
- *Deleted edges.* `n >= 400 D^(g-1)` gives `4 D^g <= Dn/100`, so fewer than
  `Dn/50 = 1.28 n` edges were deleted.
- *Colorings.* Every `x` has `mono_G(x) >= 8(n-2) - 1.28 n = 6.72 n - 16`,
  which is positive, so `E` is nonempty. Also `|E| <= |E_0| < 64 n`, so

```text
mono_G(x)/|E| >= (6.72 n - 16)/(64 n) = 0.105 - 0.25/n >= 0.1025 >= 1/10.
```

`QED`

Isolated vertices of `G` may be discarded without changing any property.
The Petersen graph (girth 5, degree 3, `tau = 3` of `15` edges) is an explicit
instance for `g in {3,4}`; the replay checks it by exhaustion. Explicit
Ramanujan graphs should give explicit instances for all `g`, through the
least-eigenvalue bound on the maximum cut. That route is not checked and
not used here.

## 4. The family H(g,N)

**Pair algebra.** For an integer `N >= 2` put `d = N^2+1`,

```text
P = |1><1|,   w = (2N, N^2-1)^T/d,   Q_N = w w^*,   g_N = (N,-1)^T/sqrt(d).
```

Then `|w| = 1`, since `4N^2 + (N^2-1)^2 = (N^2+1)^2`. The matrix `P+Q_N` has
trace `2` and determinant `w_1^2`. Its eigenvalues are therefore
`1 +- sqrt(1-w_1^2) = 1 +- w_2`, and the least one is `2/d`. Moreover
`<g_N,P g_N> = 1/d` and `<w,g_N> = (2N^2-N^2+1)/(d sqrt d) = 1/sqrt d`, so
`<g_N,Q_N g_N> = 1/d`. Finally `ker P = span|0>` is not contained in
`ker Q_N`, since `<w,|0>> = 2N/d != 0`. Hence `ker P intersection ker Q_N = {0}`.

**Definition.** Fix `g >= 3` and `N >= 2`, and take `G = (V,E)` from Lemma 4
with `m_c = |E|`. Use one qubit for each vertex and `m_c` further *pair
qubits* labelled `1,...,m_c`. The terms are:

- `h_e = |00><00| + |11><11|` on the two vertex qubits of each `e in E`;
- `P_j = P` and `Q_j = Q_N` on pair qubit `j`, for `j = 1,...,m_c`.

Write `T_j = {P_j,Q_j}` and `Pairs = union_j T_j`. There are `m = 3 m_c` terms,
and `H(g,N) = (1/m) sum_a h_a`.

**Proposition 5.** `H(g,N)` has the following properties.

1. Every term is a norm-one orthogonal projection of locality at most two on
   qubits. Vertex qubits lie in at most `512` terms and pair qubits in two.
   The entries are rationals with `O(log N)` bits.
2. A set `S` of terms is feasible if and only if both of the following hold:
   (i) some `x : V -> {0,1}` has `x_u != x_v` for every `uv in E \ S`;
   (ii) `S` meets every `T_j`.
3. `s* = tau(G) + m_c >= (11/30) m`, so the combinatorial gap is at least
   `11/30`.
4. `lambda_min(H(g,N)) = (tau(G) + 2 m_c/d)/m >= 1/30`.
5. `C_min(H(g,N)) = (tau(G) + m_c)/(tau(G) + 2m_c/d) <= 11`.

*Proof.* Item 1 is immediate from Lemma 4.

For item 2, write `H = H_V tensor (C^2)^(tensor m_c)`. For a term `a` acting
on one tensor factor `X` as `a_X`, `ker a = ker(a_X) tensor (other factors)`.
For subspaces `Y,Y'` of a factor and a finite-dimensional space `M`,
`(Y tensor M) intersection (Y' tensor M) = (Y intersection Y') tensor M`;
this follows by expanding vectors in a basis of `M`. Hence the intersection
of the kernels of the terms outside `S` on one factor `X` is
`Y_X(S) tensor (other factors)`, where `Y_X(S)` is the intersection inside
`X`. The projections onto these spaces for different factors are
`P_(Y_X) tensor I` and commute. The intersection of the ranges of commuting
projections is the range of their product, so

```text
K_S = Y_V(S) tensor Y_1(S) tensor ... tensor Y_(m_c)(S).
```

This is nonzero exactly when every factor is nonzero. Each `h_e` is diagonal
in the computational basis, with kernel spanned by the basis vectors `|x>`
with `x_u != x_v`. So `Y_V(S)` is spanned by the `|x>` satisfying every edge
outside `S`, which gives (i). `Y_j(S)` is `C^2`, `ker P`, `ker Q_N` or
`ker P intersection ker Q_N = {0}`, according to which terms of `T_j` lie
outside `S`. It is zero exactly when `S` misses `T_j`, which gives (ii).

For item 3, a feasible `S` contains the monochromatic edges of the coloring
in (i), hence at least `tau(G)` edges, and at least one term of each `T_j`.
The set of monochromatic edges of a minimizing coloring together with all
`P_j` is feasible. So `s* = tau(G) + m_c >= m_c/10 + m_c = (11/30) m`.

For item 4, `sum_e h_e` acts on `H_V`, is diagonal, and has diagonal entries
`mono_G(x)`. Its least eigenvalue is `tau(G)`. The pair sums act on distinct
factors with least eigenvalue `2/d` each. The least eigenvalue of a sum of
operators on distinct tensor factors is the sum of their least eigenvalues.
This gives the displayed value, and `tau(G) >= m_c/10 = m/30`.

Item 5 is `(CR4)` with items 3 and 4. It is at most
`(tau + m_c)/tau <= 1 + 10 = 11`. `QED`

The term matrices `Q_N` vary with `N`, as in
`qubit-pairs-have-half-gap-and-unbounded-rounder-cost`. This family does not
use a fixed finite collection of term matrices; see section 6.

## 5. The obstruction

**Lemma 5A (test vectors).** Let `U subset [m]` contain at most `g` edge
terms. Then some unit vector `v` has `<v, H_U v> = |U intersection Pairs|/d`.

*Proof.* The edges in `U` form a subgraph with at most `g` edges. A cycle in
it would be a cycle of `G` of length at most `g`, so the subgraph is a forest.
Forests are bipartite, so some `x : V -> {0,1}` has `x_u != x_v` on every
edge of `U`. Put `v = |x> tensor g_N tensor ... tensor g_N`. Each edge term
of `U` annihilates `v`. Each pair term has expectation `1/d` in `v`, by the
pair algebra. `QED`

**Theorem 6 (term flags).** Let `g >= 3`, `N >= 2` and `d = N^2+1`. If
`H(g,N)` admits a term-flag syndrome tuple satisfying (T2) and (T3), then

```text
min(g+1, d/(2 C_0)) <= 3R.
```

No restriction on `W`, the `B_a`, or the sizes of the `N(a)` is assumed.

*Proof.* `C_0 > 0` by Proposition 3. Fix `j` and put
`U_j = N(P_j) union N(Q_j)`. The set `T_j` is frustrated, so (LFC) with
`|T_j| = 2` gives `I <= 2 C_0 H_(U_j)`.

- If `U_j` contains at most `g` edge terms, evaluate at the vector of
  Lemma 5A. This gives `1 <= 2 C_0 |U_j intersection Pairs|/d`, so
  `|U_j| >= d/(2 C_0)`.
- Otherwise `|U_j| >= g+1`.

In both cases `|U_j| >= mu := min(g+1, d/(2 C_0))`. The `T_j` are pairwise
disjoint, so

```text
m_c mu <= sum_j |U_j| <= sum_j (|N(P_j)| + |N(Q_j)|) <= sum_(a in [m]) |N(a)|
        = sum_b #{a : b in N(a)} <= R m = 3 R m_c.
```

Divide by `m_c >= 1`. `QED`

**Corollary 7 (no uniform constants).** Let `C_0 >= 0` and `R >= 1` be any
constants. Every `H(g,N)` with `g >= 3R` and `N^2+1 > 6 C_0 R` admits no
term-flag syndrome tuple with these constants satisfying (T2) and (T3). All
members nevertheless satisfy Proposition 5: locality two, qubits, degree at
most `512`, combinatorial gap at least `11/30`, normalized ground energy at
least `1/30`, and `C_min <= 11`.

*Proof.* `g+1 > 3R`, and `d/(2C_0) > 3R` when `C_0 > 0`. So the minimum in
Theorem 6 exceeds `3R`, a contradiction. The case `C_0 = 0` is excluded by
Proposition 3. `QED`

Taking `g_n -> infinity` and `N_n -> infinity` gives a single infinite
family on which no uniform `(C_0,R)` exists.

**Theorem 8 (gadget flags with a union map).** If `H(g,N)` admits a
gadget-flag tuple with a union map satisfying (G2) and (G3), then

```text
min(g+1, d/(C_0 R)) <= 3 M R.
```

Hence no uniform `(C_0,R,M)` exists on the family either.

*Proof.* Proposition 3G with `T = T_j` gives `I <= C_0 R H_(U_j)`, where
`U_j = union_(i in Phi_j) N(i)` and `Phi_j = {i : phi(i) meets T_j}`. In
particular `C_0 > 0`. As before, Lemma 5A shows `|U_j| >= d/(C_0 R)` or
`|U_j| >= g+1`. For the count, the `T_j` are disjoint, so a label `i` lies
in at most `|phi(i)| <= M` of the sets `Phi_j`. Hence

```text
m_c min(g+1, d/(C_0 R)) <= sum_j |U_j| <= sum_j sum_(i in Phi_j) |N(i)|
    <= M sum_i |N(i)| = M sum_b #{i : b in N(i)} <= M R m = 3 M R m_c.   QED
```

**What is and is not used.** Clause 1 is not used: terminality, bounded
horizon, and logical-algebra requirements are dropped, and `W` may be a
Naimark dilation of arbitrary size. No efficiency is assumed. Only (T2) and
(T3), or (G2) and (G3), for the same `W,B` enter the proof. The obstruction
is therefore stronger than one against physically realized ports. It is also
independent of the SDP certificates of the primal/dual artifact.

**Remark 8A (POVM form and kernel resolutions).** The proofs of Lemma 2,
Propositions 3 and 3G and Theorems 6 and 8 use only three facts about the
effects. They are positive, `sum_S E_S = I`, and `F_a = sum_(S containing a) E_S`.
Theorem 6 therefore holds for every POVM `{E_S}` on `H` indexed by fault sets
with `E_S = 0` for infeasible `S` and
`sum_(S containing a) E_S <= C_0 H_(N(a))`.

In particular it applies to the data demanded by
`amplifier-admits-a-uniform-local-kernel-resolution`. There effects `T_S`
sum to `I`, vanish on infeasible labels, have ranges inside
`intersection_(a in S) ran A_a`, and satisfy `A_a >= delta P_(ran A_a)`. Put
`F_a = sum_(S containing a) T_S`. Then `0 <= F_a <= I`, and the range of `F_a`
lies in `ran A_a`, so `F_a = P F_a P <= P`, where `P = P_(ran A_a)`. Clause 3
of that claim gives `P <= A_a/delta`, so `F_a <= (1/delta) A_a`. Theorem 6
with `C_0 = 1/delta` gives `min(g+1, delta d/2) <= 3R`. So on `H(g,N)` with
`g >= 3R` and `delta(N^2+1) > 6R`, no kernel resolution with occurrence `R`
and spectral constant `delta` exists either.

## 6. What this shows and what it does not

**Strictness over the bare rounder.** A tuple satisfying (T2) and (T3) is a
`C_0 R`-rounder. Summing (T2) with occurrence `R` gives (SD) of
`commuting-syndrome-domination-gives-a-rounder` with `C = C_0 R`. The
fixed-measurement recovery of
`joint-syndrome-support-characterizes-exactifiability` supplies (EX) from
(T3). So `C_min <= C_0 R`, and on a family with combinatorial gap `beta` the
floor `beta/(C_0 R)` follows. Corollary 7 shows that the converse fails for
families: `C_min <= 11` uniformly, while the least admissible `C_0 R` diverges.
On unshifted instances, the requirement of
`rounder-from-local-ports-and-exactifier` is therefore strictly stronger
than the NO-side energy floor, even under a constant combinatorial gap and
bounded degree.

**The inference this kills.** Any argument that derives clauses 2 and 3,
with uniform constants, from (LPC1), a uniform NO floor or bounded rounder,
locality, local dimension and bounded degree is false. The dead route
`compatible-syndrome-effects-from-gap-and-rounder-floor` records this
inference. A construction for an unshifted amplifier must use further
structure of its outputs.

**A necessary condition for any construction.** Proposition 3 averages to
the following statement.

**Corollary 9 (averaged local frustration gap).** For `delta > 0` let
`ell(delta)` be the least cardinality of a set `U` of terms with
`lambda_min(H_U) >= delta`, with `ell(delta) = infinity` if there is none.
Suppose `H` has pairwise disjoint frustrated sets `T_1,...,T_k` with
`|T_j| <= t`. Every term-flag tuple satisfying (T2) and (T3) then has

```text
k ell(1/(C_0 min(t,R))) <= R m.
```

*Proof.* By (LFC) the set `U_(T_j)` has least eigenvalue at least
`1/(C_0 min(t,R))`, so `|U_(T_j)| >= ell(1/(C_0 min(t,R)))`. Disjointness
gives `sum_j |U_(T_j)| <= sum_a |N(a)| <= R m`. `QED`

If the NO outputs of an amplifier contain linearly many disjoint frustrated
sets of bounded size, then bounded-size subsystems with a uniform spectral
gap must exist at a bounded cost ratio. Frustration must be spectrally
robust at bounded scale. In `H(g,N)` every gapped subsystem has more than
`g` edges or at least `delta d` terms, by Lemma 5A, and this condition fails.
Positive shift meets it trivially, since then `ell(epsilon) = 1`. This agrees
with the 2026-09-11 audit: an amplifier must deliver energy or robust
soundness. Corollary 9 is a necessary condition only; it constructs nothing.

**Limitations.**

1. *Not a refutation of the target.* The target concerns the NO outputs of one
   common amplifier that also carries the YES margin. On shifted outputs the
   trivial tuple works with `C_0 = 1/epsilon` and `R = 1`, so the obstruction
   does not survive the shift. It concerns exact kernels.
2. *Varying term matrices.* `Q_N` depends on `N`. For a fixed finite collection
   of term matrices and bounded `t`, every frustrated `T` with `|T| <= t` has
   `lambda_min(H_T) >= delta_0 > 0`, uniformly over the finitely many
   incidence types. Then `N(a) = T` meets (LFC), and this method gives
   nothing. Whether constant gap, a uniform floor and a fixed finite term
   collection force uniform compatible effects is left open here. The
   fixed-term chain obstruction has fixed matrices but vanishing gap.
3. *Essentially classical instances.* `H(g,N)` is a classical cut instance
   tensored with decoupled one-qubit pairs. Its ground energy is
   `(tau(G) + 2m_c/d)/m`, so a coloring is a classical witness for low
   energy. The energy problem on the family lies in NP, and the family is not
   QMA-hard unless QMA = NP. It says nothing about quantum PCP. The graph is
   obtained by the probabilistic method, which is harmless for an obstruction
   to a general inference.
4. *Gadget maps.* Theorem 8 covers union maps `J -> union_(i in J) phi(i)` with
   `|phi(i)| <= M`. Other forms of the target's "explicit map" are not treated.

## 7. Verification boundary and sources

**What the replay checks.** The script
`experiments/gap-floor-syndrome-separation-2026-09-16/check_separation.py`
is single-threaded and uses exact `Fraction` arithmetic except for the
floating-point logarithms in item 5. Run with `timeout 600 python3` on
2026-09-16, it exits `0` with this output:

```text
pair algebra: OK for N=2..59
feasibility factorization: OK (128 subsets on triangle+2 pairs, 64 on 4-cycle+1 pair)
Petersen: girth 5, max degree 3, least monochromatic 3/15; all 1940 edge sets of size <= 4 bipartite: OK
Petersen member N=2: s*/m=2/5, lambda_min=1/5, C_min=2
Petersen member N=5: s*/m=2/5, lambda_min=6/65, C_min=13/3
Petersen member N=20: s*/m=2/5, lambda_min=137/2005, C_min=802/137
random-graph constants: log10 bounds -55.0, -238.0; failure prob < 0.250312: OK
```

It checks the following.

1. The pair algebra of section 4 for `N = 2,...,59`.
2. Item 2 of Proposition 5 on two small instances. The instances are a
   triangle with two pairs (7 qubits, 128 fault sets) and a 4-cycle with one
   pair (5 qubits, 64 fault sets). For every fault set it compares an exact
   rank test of the summed outside terms with the combinatorial rule.
3. The Petersen graph by exhaustion: girth, degrees, `tau = 3`, and
   bipartiteness of every edge set of size at most four.
4. The formulas of items 3 to 5 of Proposition 5, evaluated on the Petersen
   member for `N in {2,5,20}` from the exhaustive `tau`, together with the
   stated bounds. The full 25-qubit spectrum is not diagonalized. The
   formulas rest on the tensor-factor argument in the text.
5. The numeric inequalities in the proof of Lemma 4. These are
   `(1-ln 2)/2 > 1/8`, `D/(6(D-1)) <= 1`, the two base-10 exponents, the
   factorial bound at `Delta`, the ratio bound `D/(Delta+1) <= 1/8`, the
   final ratio `0.1025` at `n = 100`, and the sum of the failure probabilities.

**What only the text proves.** The replay checks examples and constants. The
universal statements are proved in sections 2 to 6:

- Propositions 3 and 3G;
- the probabilistic existence in Lemma 4 for all `g`;
- Proposition 5 for all `g,N`;
- Lemma 5A, Theorems 6 and 8, and Corollaries 7 and 9.

The Petersen member is not a counterexample to (T2)/(T3) with any constants,
because its girth `5` is small. It only illustrates the family's parameters.
No SDP is solved and nothing is formalized in Lean.

**Repository sources (read 2026-09-16).**

- `research/amplifier-has-compatible-local-syndrome-effects.md` (target).
- `research/artifacts/qpcp-paired-projector-obstruction-2026-09-07.md`,
  section 3 (the covering inequality).
- `research/artifacts/qpcp-syndrome-primal-dual-2026-09-07.md`, section 5
  (the sharp both-term constant `C_0 = d/4`).
- `research/artifacts/qpcp-positive-shift-audit-2026-09-11.md`, sections 3 to 7.
- `research/combinatorial-gap-and-rounder-give-energy-gap.md` (`(CR4)`).
- `research/commuting-syndrome-domination-gives-a-rounder.md` (`(SD)`, `(EX)`).
- `research/joint-syndrome-support-characterizes-exactifiability.md`.
- `research/rounder-from-local-ports-and-exactifier.md`.
- `research/locality-preserving-constant-combinatorial-gap.md` (`(LPC1)`).
- `research/fixed-term-chain-defeats-bounded-syndrome-neighborhoods.md`.
- `research/qubit-pairs-have-half-gap-and-unbounded-rounder-cost.md`.
- `research/nonorthogonal-pair-forbids-single-term-syndrome-ports.md`.

**External literature gate (2026-09-16).**

- *arXiv API* (`export.arxiv.org/api/query`, sorted by submission date).
  - `all:"combinatorial soundness" AND all:hamiltonian`: no entries.
  - `au:Bafna AND au:Nguyen`: one unrelated entry, arXiv:2609.04173v1
    (*Last Translation Benchmark*, 2026-09-03).
  - `au:Bafna AND all:quantum`: no entries.
  - `all:"gap amplification" AND all:hamiltonian`: newest entries include
    arXiv:2607.15358v1 (2026-07-16), arXiv:2606.00259v2 (2026-05-29),
    arXiv:2602.05069v2 (2026-02-04), arXiv:2510.01333v1 (*Derandomised tensor
    product gap amplification for quantum Hamiltonians*, 2025-10-01),
    arXiv:2410.13549v2 (2024-10-17) and arXiv:2403.13084v1 (*The status of the quantum PCP
    conjecture (games version)*, 2024-03-19).
  - `ti:"quantum PCP"`: newest entry arXiv:2411.00946v1 (2024-11-01).
  - None of the listed entries addresses compatible local syndrome effects,
    or joint fault feasibility for amplified Hamiltonians.
- *Web search* (three queries on the Bafna--Nguyen--Zhang title and on
  "combinatorial soundness" gap amplification): no preprint with that title
  was found. Only the entries above and older gap-amplification papers
  appeared. The arXiv author page `arxiv.org/a/nguyen_q_1` belongs to a
  different author.
- *FOCS 2026 accepted papers.* The listing of *Gap Amplification for Local
  Hamiltonians with Combinatorial Soundness* (Bafna, Nguyen, Zhang) is taken
  from `research/locality-preserving-constant-combinatorial-gap.md`. It was
  not refetched here, and no paper text was available.
- *Erdos, Graph theory and probability, Canad. J. Math. 11 (1959).* Credited
  for the high-girth deletion method. Not fetched in this attack, so the
  citation is unverified. Lemma 4 does not rely on it; its proof above is
  self-contained.
- *Explicit Ramanujan graphs* (section 3 remark). No source was fetched, and
  the remark is not used.

Titles and identifiers are recorded only from the API listing. None of the
listed papers was read in full, and none is used in a proof.

## September 20 integration

The [QPCP ledger](qpcp-integration-ledger-2026-09-20.md) includes this
separation and its graph-existence proof in the current locality audit.
It remains a counterexample to the generic inference from an energy floor,
not a refutation of a structured amplifier family. The independent
strengthened global-walk and private-composition theorems neither assume
nor construct compatible local syndrome effects.
