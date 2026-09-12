# Twisted level percolation on a hyperbolic cyclic extension is disconnected at low density

Lane `fixed-price-twisted-levels-2`, 2026-09-12. This note refutes the open claim
`fpbs-twisted-level-percolation-connected` at small density. It is an obstruction to one
graphing, not a statement about fixed price: `fpbs-hyperbolic-3-manifold-groups-fixed-price-one`
stays OPEN.

## 1. Statement

**Theorem.** Let `Gamma = N semidirect_phi Z` be a torsion-free word-hyperbolic group, with `t`
generating the `Z` factor and `t u t^-1 = phi(u)` for `u in N`. Let `S` be a finite symmetric
subset of `N \ {e}`. Then there is `delta_0 > 0` such that for every `delta in (0, delta_0)` and
every `s in S`,

    P( e and s lie in the same cluster of T_delta(N, S, phi) ) < 1,

and `T_delta(N, S, phi)` is almost surely disconnected.

Here `T_delta(N, S, phi)` is the random graph of `fpbs-twisted-level-graph-generates-cyclic-extension`:
pairs `(u, m) in N x Z` are open independently with probability `delta`, and an open pair gives
the edges `{u, phi^-m(x) u}` for `x in S`.

**Application.** For a closed hyperbolic 3-manifold `M` fibering over the circle with fibre group
`N = pi_1(S_g)` and pseudo-Anosov monodromy, `pi_1(M)` is a torsion-free cocompact Kleinian group,
hence word-hyperbolic. So the theorem applies to every finite symmetric generating set `S` of `N`,
and `fpbs-twisted-level-percolation-connected` fails for all small `delta`. The route
`fpbs-hyperbolic-3-manifold-fixed-price-via-twisted-levels` needs connectivity for arbitrarily small
`delta`, so it is invalid.

**Sanity checks against main.**
- `phi = id` (item 4 of the criterion, connected): `t` is central, so `<t>` is not malnormal and
  Step 2 below fails. Consistent.
- `F_2 = F_infinity semidirect Z` (item 5, disconnected): `F_2` is hyperbolic and `<t>` is maximal
  cyclic. The theorem agrees.

## 2. Imports (quoted from the PDFs, extracted on MSI)

**(I1) Osin, arXiv:math/0404040, Lemma 2.27.** "Suppose that a group G is given by the reduced
finite relative presentation (2.3) with respect to a collection of subgroups {H_λ}λ∈Λ. Let q be a
cycle in Γ(G,X ∪ H), p1,...,pk a certain set of isolated Hλ–components of q. Then φ(pi) ∈ ⟨Ωλ⟩
for any i = 1,...,k. Moreover, the lengths of the elements φ(p1),...,φ(pk) with respect to the
generating set Ωλ of the subgroup ⟨Ωλ⟩ satisfy the inequality Σ_{i=1}^k |φ(pi)|_Ωλ ≤ M·Area^rel(q),
where M = max_{R∈R} ||R||."

Definitions 2.19–2.21 of the same paper: an `H_λ`-component of a cycle is a maximal subpath whose
label consists of `H_λ`-letters. Two components are connected when some vertex of one and some
vertex of the other lie in the same left coset `gH_λ`. A component is isolated when no other
component is connected to it.

**(I2) Linear relative Dehn function.** Osin, arXiv:math/0404040, Definition 1.6: "We say that a
group G is hyperbolic relative to a collection of subgroups {Hλ}λ∈Λ if G is finitely presented with
respect to {Hλ}λ∈Λ and the relative Dehn function of G with respect to {Hλ}λ∈Λ is linear." So
`Area^rel(q) <= C l(q) + C'` for every cycle `q`, for a finite relative presentation. The same paper
states that one may assume finite relative presentations reduced. The wording and the finiteness
of `Omega_λ` are quoted in the citation route of `osin-isolated-components-bounded-by-relative-area`.

**(I3) Adding a maximal elementary subgroup.** This is the established claim on main
`hyperbolic-group-relative-to-maximal-elementary-subgroup`, imported from Osin, arXiv:math/0404118,
Corollary 1.7 with Definitions 1.2 and 1.4: a word-hyperbolic `G` is hyperbolic relative to
`{ {1}, E(g) }` for every `g` of infinite order. The trivial peripheral subgroup contributes no
letters, so Lemma 2.27 applies to the components labelled by `E(g)`.

## 3. The subgroup H = <t>

`Gamma` is torsion-free and hyperbolic, so `E(t)` is torsion-free and virtually cyclic, hence
infinite cyclic: `E(t) = <tau>` with `t = tau^k`. The quotient map `Gamma -> Gamma/N = Z` sends `t`
to a generator, so `k = +-1` and `E(t) = <t> =: H`. It follows that:

- (H1) `H ∩ N = {e}`. Each left coset `gH` with `g in N` contains exactly one element of `N`, so
  distinct elements of `N` lie in distinct cosets of `H`.
- (H2) The centralizer of `t^j`, `j != 0`, is contained in `E(t) = H`. So for `x in N \ {e}`, the map
  `m -> t^-m x t^m = phi^-m(x)` is injective: if `t^-m x t^m = t^-m' x t^m'`, then `x` commutes with
  `t^(m'-m)`, so `x in H ∩ N = {e}`.
- (H3) By (I3), `Gamma` is hyperbolic relative to `{ {1}, H }`. Take a finite relative presentation
  with linear relative Dehn function, and enlarge its finite relative generating set `X` so that it
  contains `S`. Adjoin the letters of `S` with one relator each, expressing them in the old generators.
  The result is still a finite relative presentation. Its relative Dehn function is equivalent to
  the old one, hence still linear: Osin, arXiv:math/0404040, p. 7, "it is independent of the choice
  of a finite relative presentation up to some equivalence relation (Theorem 2.34)". Then make it
  reduced (Definition 2.24 and the lemma after it). Each `x in S` is now a single `X`-letter
  `U_x = x`, so `L_S = 1`.

## 4. Proof

Write `S_infinity = {phi^-m(x) : m in Z, x in S}` and `C_infinity` for the graph on `N` with edges
`{u, g u}`, `g in S_infinity`. Then `T_delta` is a random subgraph of `C_infinity`.

**Step 1: witnesses.** For `g in N \ {e}`, let `I(g) = {(m, x) : phi^-m(x) = g}`. By (H2),
`|I(g)| <= |S|`. An edge `{u, v}` of `C_infinity` is in `T_delta` iff some pair in
`W(u, v) = {(u, m) : (m, x) in I(v u^-1)} ∪ {(v, m) : (m, x) in I(u v^-1)}` is open, and
`|W(u, v)| <= 2|S|`.

**Step 2: one path.** Let `gamma = (w_0, ..., w_l)` be a self-avoiding path in `C_infinity`. Then
`P(gamma in T_delta) <= (2|S|)^l delta^(l/2)`.
- If `gamma in T_delta`, there is a choice function `c` picking an open witness `c(j) in W(w_(j-1), w_j)`
  for each edge `j`. There are at most `(2|S|)^l` choice functions.
- A pair with first coordinate `w_i` lies only in the witness sets of edges `i` and `i+1`, because
  the vertices are distinct. So each chosen pair serves at most two edges, and `c` has at least
  `l/2` distinct values.
- The pairs are independent, so `P(all values of c open) <= delta^(l/2)`. Sum over `c`.

**Step 3: path count.** Let `P_l(s)` be the number of self-avoiding paths of length `l` in
`C_infinity` from `e` to `s`. Then `P_l(s) <= |S|^l 2^((K+2)(l+1))` for a constant `K` depending only
on `Gamma, S, t`.
- A path is `w_j = g_j w_(j-1)` with `g_j = phi^-(m_j)(x_j)`. Choosing one `(m_j, x_j)` per step
  overcounts paths. In `Gamma`, `phi^-m(x) = t^-m x t^m`, so `s = g_l ... g_1` says the word

      q = t^(-m_l) U_(x_l) t^(m_l - m_(l-1)) U_(x_(l-1)) ... t^(m_2 - m_1) U_(x_1) t^(m_1) U_(s)^-1

  labels a cycle in `Gamma(Gamma, X ∪ H)`, where each `t^d` with `d != 0` is one `H`-letter. Its
  relative length is at most `(L_S + 1)(l + 1)`.
- **Cosets of the components.** Trace the vertices from `e`. The component `t^(m_(j) - m_(j-1))`
  between `U_(x_j)` and `U_(x_(j-1))` runs from `g_l ... g_j t^(-m_j)` to `g_l ... g_j t^(-m_(j-1))`,
  since `t^-m x t^m = g`. So it lies in the coset `P_j H` with `P_j = g_l ... g_j = s w_(j-1)^-1`. The
  first component `t^(-m_l)` lies in `H = P_(l+1) H`, and the last, `t^(m_1)`, lies in `s H = P_1 H`.
  So the components lie in the cosets `s w_i^-1 H`, `i = 0, ..., l`.
- **Isolation.** The elements `s w_i^-1 in N` are pairwise distinct because the path is
  self-avoiding, so by (H1) the cosets are pairwise distinct. Hence every component is isolated
  (Definition 2.21). The components are separated by the nonempty `X`-words `U_x`, including across
  the cyclic junction `t^(m_1) U_s^-1 t^(-m_l)`.
- **Apply (I1) with (I2).** `sum_j |t^(d_j)|_Omega <= M Area^rel(q) <= M (C (L_S+1)(l+1) + C')`. Here
  `Omega` is a finite subset of `H`. With `M_Omega = max{|k| : t^k in Omega}`,
  `|t^d|_Omega >= |d| / M_Omega`. So `|m_1| + sum_(j=2)^l |m_j - m_(j-1)| + |m_l| <= K (l+1)`.
- **Count.** The map `(m_1, ..., m_l) -> (m_1, m_2 - m_1, ..., m_l - m_(l-1), m_l) in Z^(l+1)` is
  injective. The number of integer vectors in `Z^(l+1)` with `l^1`-norm at most `R` is at most
  `2^(l+1) binom(R+l+1, l+1) <= 2^(R + 2l + 2)`. With `R = K(l+1)` and `|S|^l` choices of the `x_j`,
  this gives the bound.

**Step 4: the two-point bound.** A cluster containing `e` and `s` contains a self-avoiding open path
between them. By Steps 2 and 3,

    P(e <-> s) <= sum_(l>=1) |S|^l 2^((K+2)(l+1)) (2|S|)^l delta^(l/2) = A sum_(l>=1) rho^l,

with `A = 2^(K+2)` and `rho = 2^(K+3) |S|^2 sqrt(delta)`. Choose `delta_0` with `A rho/(1-rho) < 1`
at `delta = delta_0`. Then `P(e <-> s) < 1` for `delta < delta_0`.

**Step 5: almost sure disconnection.**
- Right translation `(u, m) -> (u w, m)` preserves the product law and maps `T_delta` isomorphically
  onto its right translate by `w^-1`, so the event "connected" is `N`-invariant.
- `N` acts freely on `N x Z` with infinite orbits, so this Bernoulli action is mixing, hence ergodic,
  and the event has probability 0 or 1.
- It has probability at most `P(e <-> s) < 1`, so it is 0.

## 5. What this does and does not settle

- **Refuted:** `fpbs-twisted-level-percolation-connected` (every closed fibered hyperbolic
  3-manifold, every `S`, all `delta < delta_0`). By item (1) of
  `fpbs-twisted-level-graph-generates-cyclic-extension`, the transport graphing
  `{t} ∪ {s|_A}` with `A = {x(e) < delta}` does not generate the Bernoulli orbit relation for small
  `delta`.
- **Invalidated:** `fpbs-hyperbolic-3-manifold-fixed-price-via-twisted-levels`.
- **Not touched:** fixed price itself; and graphings `{t} ∪ {s|_A}` for other Borel sets `A` of
  small measure. Step 2 is the only place independence is used. The path count of Step 3 is
  combinatorial and holds for every `A`. A repair must use a set `A` whose open levels are strongly
  correlated along `t`-orbits: for a path, the probability that all chosen witnesses are open must
  not decay like `delta^(l/2)`.
- **Mechanism.** In the product case `t` is central, so a vertex gets infinitely many chances at the
  same neighbour. In a hyperbolic extension, `<t>` is malnormal and quasiconvex. Relative
  hyperbolicity charges long `t`-excursions linearly (Step 3), so the return graph behaves like
  sparse percolation on a fine hyperbolic graph with exponentially many paths between neighbours.
- **Scope of the hypothesis.** The theorem needs only torsion-free hyperbolicity of `Gamma`. So it
  also applies to hyperbolic free-by-cyclic groups. No novelty or priority is claimed. The argument
  is elementary once (I1)–(I3) are granted.
