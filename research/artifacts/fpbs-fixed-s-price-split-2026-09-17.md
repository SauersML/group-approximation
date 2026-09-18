# Fixed-S price split of the Morse-deficit hole (2026-09-17, swarm-0917-w5-fp-morse)

Written deduction. Nothing here is formally verified.

## 0. Setting

- `Gamma` is a countably infinite group with a finite symmetric generating set `S`, `1 ∉ S`.
- `(X, mu)` is standard non-atomic. `a` ranges over free pmp actions of `Gamma` on `X`. `b` is the Bernoulli shift.
- `Phi_S^a` is the Cayley graphing, with edges `{x, a(t)x}` for `t ∈ S`. A generating subgraphing is a Borel
  symmetric edge set `E ⊆ Phi_S^a` whose components are the `R_a`-classes. Writing `A_t = {x : {x, a(t)x} ∈ E}`,
  so that `A_(t^-1) = a(t)A_t`, its cost is `c(E) = (1/2) sum_(t ∈ S) mu(A_t)`.
- `C_sub^a(S)` is the infimum of `c(E)` over generating subgraphings, as in
  `fpbs-cost-is-limit-of-cayley-subgraphing-costs`.
- `c_inv(S)` is half the infimum of `E deg_omega(1)` over `Gamma`-invariant random connected spanning subgraphs
  `omega` of `Cay(Gamma, S)`. This is the "`G`-cost of `G`" of Beringer–Pete–Timár (arXiv:1609.07043) for
  `G = Cay(Gamma, S)`.
- `cost(Gamma) = inf_a C(a)`, `beta_1 = beta_1^(2)(Gamma)`, and `a_inf` is the Burton–Kechris maximum for `≼`.
  `a_inf` is free because the free actions are upward closed (`burton-kechris-cost-usc-and-maximum-action`, item 3).
- "Hole at `S`" means `lim_L m_S(P_L) = 0`, the statement of `fpbs-morse-deficit-vanishes-for-full-presentations`
  at `S`.
- "`S`-fixed price" means that `C_sub^a(S)` is the same for all free `a`.

## 1. Lemma H1: `C_sub(S)` is antitone under weak containment

**Lemma.** If `a ≼ a'` are free, then `C_sub^(a')(S) <= C_sub^a(S)`. Consequently, for every free `a`,
`C_sub^(a_inf)(S) <= C_sub^a(S) <= C_sub^b(S)`.

*Proof.*

1. **Setup.** Let `E` be a generating subgraphing of `Phi_S^a` with sets `A_t` and cost `c`. For `N >= 1` and
   `t ∈ S`, and for any action `c'` of `Gamma` on `X`, let `W_N(t)` be the finite set of words
   `(t_1, ..., t_k)` in `S` with `k <= N` and `t_k ... t_1 = t` in `Gamma`. Put

   `D_t^N(c') = X \ union_(w ∈ W_N(t)) intersect_(i=1..k) [ c'(t_(i-1)...t_1)^(-1) (A_(t_i) ∪ c'(t_i)^(-1) A_(t_i^-1)) ]`.

   This is a finite Boolean combination of the sets `c'(gamma)A_u` with `|gamma|_S <= N + 1`. If `y ∉ D_t^N(c')`,
   the edges `{z, c'(u)z}` with `z ∈ A_u` join `y` to `c'(t)y` by a path of length `<= N`.
2. **Tail at `a`.** At `c' = a`, freeness and generation give `mu(D_t^N(a)) -> 0` as `N -> infinity`. Every path in
   `Phi_S^a` from `x` to `a(t)x` has label word equal to `t` in `Gamma`.
3. **Approximating conjugates.** By Burton–Kechris Theorem 2.3 (imported in
   `burton-kechris-cost-usc-and-maximum-action`, item 1), there are actions `c_n` conjugate to `a'` with `c_n -> a`
   in the weak topology. Then `mu(c_n(gamma)A Δ a(gamma)A) -> 0` for each Borel `A` and each `gamma`. So the measure
   of every fixed finite Boolean combination of translates converges. In particular:
   - `mu(D_t^N(c_n)) -> mu(D_t^N(a))`;
   - `mu(c_n(t)^(-1)A_(t^-1) Δ A_t) -> mu(a(t)^(-1)A_(t^-1) Δ A_t) = 0`.
4. **Patched subgraphing.** In `c_n` take the edges `{z, c_n(u)z}` for `z ∈ A_u`, together with
   `{z, c_n(t)z}` for `z ∈ D_t^N(c_n)`. Every `y` is then joined to `c_n(t)y` for all `t ∈ S`, and `S` generates
   `Gamma`, so this generates `R_(c_n)`. Its cost is at most
   `(1/2) sum_t [ mu(A_t) + mu(c_n(t)^(-1)A_(t^-1) \ A_t) ] + sum_t mu(D_t^N(c_n))`, which tends to
   `c + sum_t mu(D_t^N(a))` as `n -> infinity`.
5. **Limit.** `C_sub(S)` is a conjugacy invariant. Letting `n` and then `N` go to infinity gives
   `C_sub^(a')(S) <= c`. Take the infimum over `E`.
6. **Consequence.** The bounds follow from `a ≼ a_inf` (maximality) and `b ≼ a`
   (`abert-weiss-free-actions-weakly-contain-bernoulli`). `QED`

The patch uses only `S`-edges. That is the point: the Kechris proof of monotonicity of cost adds arbitrary group
elements, and here the backup edges already lie in `Phi_S`.

## 2. Lemma H2: the invariant Cayley cost is the weak-maximum end

**Lemma.** `c_inv(S) = inf_a C_sub^a(S) = C_sub^(a_inf)(S)`.

*Proof.*

- **`<=`.** Take a generating subgraphing `E` of `Phi_S^a` and `x ~ mu`. Let `omega_x` be the graph on `Gamma` with
  edge `{gamma, gamma t}` iff `{gamma^(-1)x, t^(-1)gamma^(-1)x} ∈ E`. Then `omega_(a(g)x) = g.omega_x`, so the law
  is invariant. By freeness, `gamma -> gamma^(-1)x` is a graph isomorphism from `omega_x` onto the `E`-component of
  `x`, and that component is the whole orbit. So `omega_x` is connected and spanning, with
  `E deg(1) = 2 c(E)`.
- **`>=`.** Take an invariant connected spanning `omega` with law `nu`. Let `a` be the diagonal shift on
  `({0,1}^(edges) x [0,1]^Gamma, nu x lambda^Gamma)`, which is free because of the Bernoulli factor. Put
  `E = {{x, a(t)^(-1)x} : {1, t} ∈ omega(x)}`. Its components are the images of the components of `omega`, so it
  generates, and `c(E) = E deg_omega(1) / 2`.
- **Last equality.** It follows from Lemma H1. `QED`

## 3. Theorem H3: the split

**Theorem.** The following are equivalent.
- (i) The hole holds at `S`: `lim_L m_S(P_L) = 0`.
- (ii) `C_sub^b(S) = 1 + beta_1`.
- (iii) `S`-fixed price holds, and `c_inv(S) = 1 + beta_1`.

Moreover, (i) implies `c_inv(S) = cost(Gamma) = C(b) = 1 + beta_1`. At `Cay(Gamma, S)` this is a positive answer to
the question that Beringer–Pete–Timár record as not known in general.

*Proof.*

1. **Gaboriau bound.** For every free `a`, `1 + beta_1 <= C(a) <= C_sub^a(S)`. The first inequality is
   `fpbs-graphing-cost-betti-cycle-dimension-identity`. The second holds because subgraphings are graphings.
2. **(i) ⟺ (ii).** By (G) of `fpbs-cost-is-limit-of-cayley-subgraphing-costs`, (i) is equivalent to
   `C(b) = 1 + beta_1` together with `C_sub^b(S) = C(b)`. By step 1, that conjunction is equivalent to (ii).
3. **(ii) ⟹ (iii).** For free `a`, step 1 and Lemma H1 give `1 + beta_1 <= C_sub^a(S) <= C_sub^b(S) = 1 + beta_1`.
   So all the `C_sub^a(S)` are equal. By Lemma H2, `c_inv(S) = 1 + beta_1`.
4. **(iii) ⟹ (ii).** `C_sub^b(S) = C_sub^(a_inf)(S) = c_inv(S) = 1 + beta_1`.
5. **Moreover.** Burton–Kechris Theorem 7.1 gives `C(a_inf) = cost(Gamma)`, so
   `1 + beta_1 <= cost(Gamma) <= c_inv(S) = 1 + beta_1`, and `C(b)` is squeezed in the same way. `QED`

**The two prerequisites fail independently, in principle.**
- (P1) `S`-fixed price says that the two weak-containment extremes agree: `C_sub^b(S) = C_sub^(a_inf)(S)`.
- (P2) `c_inv(S) = 1 + beta_1` is an invariant-percolation statement. No factor-of-iid structure is involved.
- (P2) holds at every `S` for Kazhdan groups (Section 4), where the hole is still open. So any failure of the hole
  there is a failure of (P1).
- A failure of (P2) at some `S` would answer the Beringer–Pete–Timár question negatively. It would also refute the
  hole at that `S`, whatever the truth of the cost–Betti target.

## 4. Literature status of the two prerequisites (verbatim)

Read 2026-09-17 from arXiv HTML, fetched with curl and stripped of tags.

- **Beringer, Pete, Timár, arXiv:1609.07043.** "The cost of a group $\mathbb{G}$ is defined as half of the infimum
  of the expected degrees of its invariant connected spanning graphs. The $\mathbb{G}$ -cost of a transitive graph $G$
  may be defined similarly, over $\mathbb{G}$ -invariant random connected spanning sub graphs of $G$ , where
  $\mathbb{G}\leq Aut(G)$ is a vertex-transitive subgroup of graph-automorphisms. It is not known in general that, if
  we first fix a Cayley graph $G$ of $\mathbb{G}$ , then the $\mathbb{G}$ -cost of $G$ is always as small as the cost
  of $\mathbb{G}$ (which is the cost of the complete graph on $\mathbb{G}$ )."
- **Hutchcroft, Pete, arXiv:1810.11015, Theorem 1.2.** "Let $\Gamma$ be a countably infinite Kazhdan group. Then
  $\Gamma$ has cost $1$ ." They also write: "The proof of Theorem 1.2 establishes that for every $\varepsilon>0$ and
  every finite symmetric generating set $S$ of $\Gamma$ , there is a $\Gamma$ -invariant measure on connected,
  spanning subgraphs of the associated Cayley graph with average degree at most $2+\varepsilon$ ." And: "Our
  construction is very far from being a factor of i.i.d., and therefore seems unsuitable to study
  $\operatorname{cost}^{*}(\Gamma)$".

**Kazhdan corollary.**
- `c_inv(S) = 1` at every `S`, by the second Hutchcroft–Pete sentence.
- Then `beta_1 = 0` by step 1 of Theorem H3 and Lemma H2 (`1 + beta_1 <= c_inv(S)`).
- So (P2) holds, and for Kazhdan `Gamma` the hole at `S` is equivalent to `S`-fixed price for `(Gamma, S)`, that is,
  to `C_sub^b(S) = 1`.
- The Hutchcroft–Pete sentence on `cost*` records that the passage from `a_inf` to `b` is exactly what their
  construction cannot do.

**Updates.**
- The `(Q3)` paragraph of `research/artifacts/fpbs/docs/bernoulli-morse-collapse-criterion.md` says "We know no
  reference either way". The Beringer–Pete–Timár sentence is a reference for the invariant half: at a single `S`,
  (P2) is at least as strong as their unknown statement, and the hole at `S` implies it.
- For amenable `Gamma`, the same paper notes that cost 1 is achieved inside every Cayley graph, so (P2) holds there.

## 5. Biography of a minimal counterexample, and dead ends

Suppose the hole fails at `(Gamma, S)`, with `delta = C_sub^b(S) - 1 - beta_1 > 0`. Then:

1. **Transfer.** By Lemma H1, `C_sub^a(S) <= 1 + beta_1 + delta` for every free `a`. Every free action is at least
   as good at `S` as Bernoulli, so a counterexample is visible only at the factor-of-iid end.
2. **Two channels.** Either (P2) fails, which gives a Beringer–Pete–Timár counterexample, or (P2) holds and (P1)
   fails. In the second case `C_sub^b(S) > C_sub^(a_inf)(S) = cost(Gamma) = 1 + beta_1`, and cost is attained inside
   `Cay(Gamma, S)` invariantly but not as a factor of iid.
   - For Kazhdan groups only the second channel exists.
   - By upward closure of `(Q3)(S)`, both channels close as `S` grows: `inf_S C_sub^b(S) = C(b)`.
3. **Dead: percolation-cluster certificates are not necessary.** One tries to certify `C_sub^b(S) <= 1 + beta_1` by
   Bernoulli clusters, using `fpbs-sparse-spine-cost-bound`: the unique cluster plus arrows toward it, all `S`-edges.
   - This gives `C_sub^b(S) <= 1 + theta_S(p)(d/2 - 1)` on the uniqueness phase.
   - It dies at infinitely-ended groups. For `Gamma = F_2`, `S = {a^±, b^±, (ab)^±}`: `p_u = 1`, so the only
     certificate costs `d/2 = 3` against `1 + beta_1 = 2`. Yet the hole holds there, because the free-basis edges form a
     treeing inside `Phi_S^b` of cost 2.
   - It certifies the hole at `S` only when `theta_S(p_u+)(d/2 - 1) <= beta_1`. For `beta_1 = 0` that requires no
     nonuniqueness phase at `S`, which is Benjamini–Schramm-conjecturally never for nonamenable `Gamma`.
4. **Dead: hyperfinite coarsening does not trivialize the Cayley question.**
   - The move is to pass to the relative cost over an aperiodic hyperfinite `H ⊆ R_b`, which equals `C(b) - 1` there,
     and hope that `H`-classes absorb most `S`-edges.
   - It dies at the invariant `1 - rho_S` (spectral radius). This is a sketch, not a written proof. Suppose `mu(x ~_H a(t)x) >= 1 - eps` for all `t ∈ S`.
     Reiter functions for `H` on classes then give almost invariant vectors in a representation weakly contained in
     `lambda`, contradicting `rho_S < 1` once `eps` is small relative to `1 - rho_S`.
   - So a positive density of `S`-edges always crosses `H`-classes, and the relative problem is the original one.
   - This is the same obstruction as the Voronoi-contraction attempt: paths cross many cells.
5. **Dead: stepwise weak-containment transfer of the Hutchcroft–Pete scheme.** This would supply (P1) for Kazhdan
   groups. It is already killed by `fpbs-hp-condensation-bernoulli-exit` (A)–(B): exact cluster thinning leaves the
   closure `W_b` at a finite stage for every nonamenable `Gamma`.
6. **Open recipe.** A counterexample to the hole is the same as one of:
   - a Cayley graph whose invariant cost exceeds the group cost (channel P2);
   - a group and generating set at which invariant sparse connected subgraphs exist, but no factor-of-iid ones, beyond
     what `inf_S` repairs (channel P1).

   The first is the Beringer–Pete–Timár question. The second, for Kazhdan groups, is the `cost*` question of
   Hutchcroft–Pete localized at `S`.
