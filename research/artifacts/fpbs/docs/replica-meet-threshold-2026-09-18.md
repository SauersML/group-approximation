# Replica meet thresholds: a qualitative sandwich between p_k and p_u

swarm-0917-w13 (transplanter, reframing), 2026-09-18.

## 0. Setting and definitions

`G` is a connected, locally finite, transitive graph with root `o`. For `k >= 1`
let `omega_1, ..., omega_k` be independent Bernoulli(`p`) bond configurations
with joint law `P_p^{(k)}`. `K^i(x)` denotes the cluster of `x` in `omega_i`.

**Meet relation.** Write `x ≈_k y` iff `x <-> y` in every `omega_i`. This is an
equivalence relation on `V(G)`, and its class of `x` is

```text
M_k(x) = K^1(x) ∩ ... ∩ K^k(x).
```

It is the meet of the `k` cluster partitions. `Aut(G)` acts diagonally on
`(omega_1, ..., omega_k)`, the joint law is invariant, and `M_k(gx)(g omega) = g M_k(x)(omega)`.

**Meet threshold.**

```text
p_cap^(k) = sup{ p in [0,1] : P_p^(k)( |M_k(o)| = infinity ) = 0 }.
```

Write `p_cap = p_cap^(2)`. `Z_k(p) = sum_x tau_p(o,x)^k` and
`p_k = sup{p : Z_k(p) < infinity}` are as in
`fpbs-lq-threshold-power-monotonicity`.

The event `{|M_k(o)| = infinity}` is increasing in each `omega_i`. Under the
standard monotone coupling of all `P_p` (uniform edge labels, one family per
replica), its probability is nondecreasing in `p`. So the set of `p` where
`M_k(o)` is a.s. finite is an interval that starts at 0, with right end
`p_cap^(k)`.

## 1. Theorem (meet sandwich)

Let `G` be as in Section 0, infinite. For every integer `k >= 1`:

1. **(Mean.)** `E_p^(k) |M_k(o)| = Z_k(p)`. Hence `p_c <= p_k <= p_cap^(k)`.
2. **(Thinned cluster.)** `p_cap^(k) <= p_c^(1/k)`.
3. **(Uniqueness.)** `p_cap^(k) <= p_u`. (Uses simultaneous uniqueness above
   `p_u` from `fpbs-cluster-count-trichotomy`.)
4. **(Hierarchy.)** `p_cap^(k) <= p_cap^(k+1)`, so
   `p_cap^(infty) := sup_k p_cap^(k) = lim_k p_cap^(k) <= p_u`.
5. **(Trees.)** On the `d`-regular tree `T_d`, `d >= 3`,
   `M_k(o)` is the `o`-cluster of `omega_1 ∧ ... ∧ omega_k`. Hence
   `p_cap^(k) = p_k = (d-1)^(-1/k)`, the finite set is the closed interval
   `[0, p_cap^(k)]`, and `p_cap^(infty) = 1 = p_u(T_d)`. In particular
   `p_c < p_cap < p_u` on `T_d`.

### Proofs

**Item 1.** By Tonelli and independence of the replicas,

```text
E|M_k(o)| = sum_x P(x in K^1(o), ..., x in K^k(o)) = sum_x tau_p(o,x)^k = Z_k(p).
```

If `Z_k(p) < infinity` then `|M_k(o)| < infinity` a.s. So every `p < p_k` lies
in the finite interval, giving `p_k <= p_cap^(k)`. For `p < p_c`,
`Z_k <= Z_1 = chi(p) < infinity` (since `tau <= 1`), so `p_c <= p_k`.

**Item 2.** Let `eta = omega_1 ∧ ... ∧ omega_k` (edgewise minimum). By
independence `eta` is Bernoulli(`p^k`). An `eta`-open path is open in every
`omega_i`, so `K_eta(o) ⊆ M_k(o)`. If `p^k > p_c` then
`P(|K_eta(o)| = infinity) = theta(p^k) > 0`, so `M_k(o)` is infinite with
positive probability and `p >= p_cap^(k)`. Hence `p_cap^(k) <= p_c^(1/k)`.

**Lemma 1.1 (invariant finite sets are null at the root).** Let `S` be a
random subset of `V(G)` whose law is invariant under a group `Gamma` of
automorphisms acting transitively on the infinite set `V(G)`. Then
`P(o in S, |S| < infinity) = 0`.

*Proof.* Fix `n >= 1` and let `E_n = {|S| = n}`, an invariant event. For
`x in V`, choose `g in Gamma` with `g o = x`. Invariance gives
`P(x in S, E_n) = P(o in S, E_n) =: c_n`. By Tonelli,

```text
n P(E_n) = E[|S| ; E_n] = sum_x P(x in S, E_n) = c_n · |V| .
```

The left side is at most `n`, and `|V| = infinity`, so `c_n = 0`. Summing over
`n >= 1` gives the claim. ∎

**Item 3.** Let `p > p_u`. By `fpbs-cluster-count-trichotomy` (item 2,
Häggström–Peres and Schonmann), each `omega_i` a.s. has exactly one infinite
cluster `I^i`. Also `p > p_u >= p_c`, so `theta(p) > 0`. Put
`S = I^1 ∩ ... ∩ I^k`. It is a measurable function of `(omega_i)` that commutes
with the diagonal action of `Aut(G)`, so its law is `Aut(G)`-invariant.
`Aut(G)` is transitive, and `V` is infinite. On `{o in S}` we have
`K^i(o) = I^i` for each `i`, hence `M_k(o) = S`. Then

```text
P(|M_k(o)| = infinity) >= P(o in S, |S| = infinity) = P(o in S) = theta(p)^k > 0 .
```

The middle equality is Lemma 1.1, and the last one is independence. So
`p >= p_cap^(k)` for every `p > p_u`, which gives `p_cap^(k) <= p_u`.

**Item 4.** `M_(k+1)(o) ⊆ M_k(o)` pointwise, with the first `k` replicas
shared. If `M_k(o)` is a.s. finite at `p`, then so is `M_(k+1)(o)`. The
limit exists by monotonicity and is at most `p_u` by item 3.

**Item 5.** In a tree the path from `o` to `x` is unique, so
`x in K^i(o)` iff that path is `omega_i`-open. Then `x in M_k(o)` iff the path
is open in all replicas, iff it is `eta`-open. So `M_k(o) = K_eta(o)` with `eta`
Bernoulli(`p^k`).

- On `T_d` the `o`-cluster of Bernoulli(`r`) is finite a.s. iff
  `r <= 1/(d-1)`. The subtrees below the root's neighbours are Galton–Watson
  with Binomial(`d-1`, `r`) offspring, and a nondegenerate GW tree survives iff
  its mean `(d-1) r` exceeds 1.
- Hence `|M_k(o)| < infinity` a.s. iff `p^k <= 1/(d-1)`, so
  `p_cap^(k) = (d-1)^(-1/k)` and the finite set is closed.
- By item 1, `Z_k(p) = E|K_eta(o)| = chi(p^k)`, which is finite iff
  `p^k < 1/(d-1)` (a GW mean computation). So `p_k = (d-1)^(-1/k)` as well, in
  agreement with `fpbs-lq-threshold-power-monotonicity`.
- `p_cap^(k) -> 1 = p_u(T_d)`. For `k = 2`,
  `p_c = 1/(d-1) < (d-1)^(-1/2) = p_cap < 1`. ∎

**Corollary 1.2 (positions).**

- `p_c < p_2` implies `p_c < p_cap`. So every class with `p_c < p_(2->2)` has
  `p_c < p_cap`, since `p_(2->2) <= p_2` by
  `fpbs-lq-threshold-power-monotonicity`.
- [Q_fin] (`fpbs-two-point-some-lq-above-pc-universal`) implies that
  `p_c < p_cap^(k)` for some `k`.
  - [Q_fin] supplies `p > p_c` and `k` with `E|∩_i K^i_inf(o)| < infinity`.
  - If `|M_k(o)| = infinity` then every `K^i(o)` is infinite, so
    `M_k(o) = ∩_i K^i_inf(o)`.
  - Hence `M_k(o)` is a.s. finite at that `p`.
- [Q] (`fpbs-two-point-lq-threshold-gap-universal`) implies `p_c < p_cap^(3)`,
  through `Z_3`. [Q] does not give `p_c < p_cap^(2)` by this argument, because
  [Q] allows `q_0 = 2`.
- `p_c < p_cap^(k)` for some `k` implies `p_c < p_u`, by item 3.

## 2. The new hole and the chain

**[cap_fin]** (`fpbs-replica-meet-threshold-gap-universal`): on every
nonamenable Cayley graph, `p_c < p_cap^(k)` for some `k`.

```text
p_c < p_(2->2)  =>  p_c < p_2  =>  [Q]  =>  [Q_fin]  =>  [cap_fin]  =>  p_c < p_u
                          \______________________________/^
                            (p_c < p_2 gives k = 2 directly)
```

What is new is that [cap_fin] is **qualitative**. It asks only that the meet
of `k` replicas be a.s. finite at one `p > p_c`. It tolerates
`E|M_k(o)| = Z_k(p) = infinity` for every `k`, that is, `q_0 = infinity`.
[Q_fin] asks for finite expectation. A priori [cap_fin] could hold on a graph where
[Q_fin] fails (no example is known either way), and a proof of it may use ergodic or a.s. tools (mass
transport, indistinguishability, insertion tolerance) that give no moment
bounds.

**Calibration.** On `T_d` the three values `p_2`, `p_cap` and `sqrt(p_c)`
agree, and `p_cap < p_u = 1`. So the tree saturates items 1 and 2,
and item 3 is strict there.

## 3. Where the reframing dies for [Q] and for [cap_fin]

1. **For [Q].** The meet reframing produces a hole that is *weaker* than [Q]
   and [Q_fin], not a proof of either. [Q] follows from `p_c < p_cap^(k)` only
   if an a.s.-finite meet can be upgraded to a finite mean. No such upgrade is
   available: `E|M_k| = Z_k` is exactly the l^k question.
2. **Right germ.** The finite set `A_k = {p : |M_k(o)| < infinity a.s.}`
   contains `[0, p_c]` by `fpbs-critical-no-infinite-cluster` (BLPS), since
   `M_k(o) ⊆ K^1(o)`. [cap_fin] is exactly the statement that `p_c` is interior
   to `A_k` for some `k`. This is the same openness through `p_c` that
   stopped every attempt on [Q] (Russo–BK, critical import, thinning,
   pivotal split).
3. **Where the non-tree information sits.** On trees `M_k(o)` *equals* the
   Bernoulli(`p^k`) cluster (item 5). So there the meet has the Bernoulli
   majorant `K_eta` at parameter `p^k < p`, and [cap_fin] is immediate.
   - On a graph with cycles, `M_k(o) \ K_eta(o)` is the set of points reached
     from `o` along *different* paths in different replicas.
   - `M_k(o)` is then not the cluster of any edge configuration built from
     the `omega_i`. The only coupling majorant available in general is
     `M_k(o) ⊆ K^1(o)`, at parameter `p` itself, which is useless above
     `p_c`.
   - A proof of [cap_fin] must therefore control the multi-path set
     `M_k \ K_eta` at `p_c + 0`. This is the replica form of the exponent
     circle in `lq-threshold-power-monotonicity-2026-09-17.md`, Section 5:
     thinning and coupling are equalities on trees and give nothing more.
4. **Not lower semicontinuous in the marked-group topology.** Let
   `S_m = F_2/F_2^(m)`, as in the w10 attempt on
   `fpbs-two-point-lq-threshold-gap-universal`. The `S_m` are amenable, so
   `p_u = p_c` there, and item 3 gives `p_cap^(k)(S_m) = p_c(S_m)`. But
   `p_cap^(k)(T_4) = 3^(-1/k) > 1/3`. So no ball-local certificate of
   `p_c < p_cap^(k)` exists. This remark uses the same imports as the w10
   attempt and is not part of the established claim.

## 4. The hierarchy question and a toy obstruction

**Question [cap_inf].** Is `p_cap^(infty) = p_u` on every nonamenable Cayley
graph? It holds on `T_d` (item 5).

- If it holds, then for every `p < p_u` some finite number of replicas has
  a.s. finite meet. This is a replica characterisation of nonuniqueness.
- It would **not** give BS by itself. It says nothing about whether `p_u > p_c`.

**Toy obstruction (not a percolation model, not invariant).** Pointwise decay
of the one-replica marginal cannot decide [cap_inf].

- Let `V` be the disjoint union of sets `V_j`, `j >= 3`. Split each `V_j` into
  `m_j = ⌈log j⌉` nonempty blocks `B_(j,1), ..., B_(j,m_j)`.
- Let `K = ∪_j B_(j,U_j)`, with the `U_j` independent and uniform. Then
  `P(x in K) = 1/m_j -> 0`.
- For `k` independent copies, the event "all copies pick the same block at
  level `j`" has probability `m_j^(-(k-1))`. These events are independent in
  `j`.
- `sum_j (log j)^(-(k-1)) = infinity`, so by the second Borel–Cantelli lemma
  the copies agree at infinitely many levels. Hence the `k`-fold intersection
  is infinite a.s., for every `k`.

So a proof of [cap_inf] or [cap_fin] must use decorrelation of the cluster
across scales, not decay of `tau` alone. By item 1, `tau` alone determines
exactly the means `Z_k`.

## 5. Status

- **Established:** items 1–5 and Corollary 1.2. They are self-contained apart
  from the imports `fpbs-cluster-count-trichotomy` (item 3) and
  `fpbs-critical-no-infinite-cluster` (Section 3, item 2 only).
- **Open:**
  - [cap_fin], new hole `fpbs-replica-meet-threshold-gap-universal`;
  - [cap_inf], a question only, with no node.
- **Dead for [Q]:** the reframing yields a weaker sibling, not [Q]. See
  Section 3, items 1–3.
