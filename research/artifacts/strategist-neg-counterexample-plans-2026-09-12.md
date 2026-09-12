# Strategist (negative side): untried counterexample routes, screened and ranked

Lane `w3-strategist-neg`, 2026-09-12. The job was to find the most decisive counterexample route that nobody
has tried. Section 1 records the candidates that die on arrival or turn out to be existing targets under a
new name, so nobody re-derives them. The later sections give the plans that survive the screen, ranked.

## 1. Screened candidates

### 1.1 Alphabet-increasing embeddings are impossible

Suppose |B| > |A| and there is an injective automaton `B^G -> A^G`. Composing it with the inclusion
`A^G -> B^G` would give a strict automaton on `B^G`. But no such automaton exists, for any group `G`.
- The fixed points of the shift action on `A^G` are exactly the constant configurations. `G` acts
  transitively on itself, so a fixed configuration takes one value everywhere.
- An equivariant map sends fixed points to fixed points, and an injective one does so injectively.
- So `|B| <= |A|`.

This is the embedding form of `full-shifts-with-different-alphabets-are-not-conjugate`. No route exists here.

### 1.2 Copy and pullback transfers are routing

- The bicyclic monoid `<p, q | qp = 1>` carries the injective, non-surjective automaton
  `tau(x)(m) = x(mq)`, because `m -> mq` is onto but not injective.
- Nonunimodular Hecke pairs `(G, H)` carry the analogous pullback along `gH -> gkH`, when `k^-1 H k` has
  index 2 in `H`.
- The end-fixing tree carries the parent copy `tau(x)(v) = x(p(v))`.

All three move symbols without computing with them.
- Over a group acting on itself, every equivariant map of the index set is a bijection `g -> gm`, as the
  calibration in `end-fixing-tree-symmetries-carry-strict-automata` notes.
- A transferred rule that still reads one symbol per output site falls under the routing screen
  `certificate-controlled-routing-is-surjunctive`. That scope is to be checked against that node's
  hypotheses; this section records a screen, not a theorem.

A monoid-to-group or Schreier-to-group induction must add arithmetic mixing. That puts it back in the
linear families or the nonlinear balance families. No new route.

### 1.3 Homomorphic automata over solvable group alphabets reduce to stable finiteness

**Claim** `homomorphic-solvable-alphabet-ca-reduce-to-stable-finiteness`. Let `K` be a finite solvable group
and `G` any group.
- If `F_p[G]` is stably finite for every prime `p` dividing `|K|`, then every injective automaton
  `K^G -> K^G` that is a group homomorphism is surjective.
- Conversely, a non-directly-finite `M_n(F_p[G])` gives a strict homomorphic automaton on `(F_p^n)^G`.

**Proof.**
1. **The local rule is a homomorphism.** It is `mu(x|_S) = tau(x)(1)`, and `tau` is a homomorphism, so
   `mu : K^S -> K` is one.
2. **Characteristic subgroups are preserved.** `[K^S, K^S] = [K,K]^S`, so `mu` maps `(K^(i))^S` into
   `K^(i)` for every term of the derived series. The same holds for the p-primary components and the
   subgroups `p^j L` of an abelian layer `L`. So `tau` preserves the filtration
   `K^G >= (K')^G >= ...`, refined until every layer is an `F_p`-vector space, and it induces homomorphic
   automata on the layers.
3. **The induction step.** Take a normal characteristic subgroup `N` with quotient `Q = K/N`, and suppose
   `tau` is injective.
   - `tau_N` is injective. By induction it is surjective.
   - If `tau(x)` lies in `N^G`, write `tau(x) = tau(n)` with `n` in `N^G`. Injectivity gives `x = n`, so
     `tau_Q` is injective. By induction it is surjective.
   - Given `y`, choose `x` with `tau_Q(xbar) = ybar`. Then `y = tau(x) n'` with `n'` in `N^G`. Writing
     `n' = tau(n)` gives `y = tau(xn)`.
4. **Base case.** An `F_p`-linear automaton on `(F_p^n)^G` that is injective is surjective when
   `M_n(F_p[G])` is directly finite. This is the standard equivalence between linear surjunctivity and
   stable finiteness (Ceccherini-Silberstein–Coornaert). The converse is
   `stable-finiteness-failure-refutes-surjunctivity`.

**Scope.**
- Nonabelian simple layers need a separate argument. A homomorphism `T^S -> T` with `T` nonabelian simple
  is trivial or a coordinate projection composed with an automorphism, since `T^2` does not embed in `T`.
  That forces permutation-type rules on such layers. Extending the reduction to all finite `K` is left
  open.
- **Consequence:** noncommutative group alphabets give no escape from the linear gates.

### 1.4 Stabilized Goodearl–Handelman certificates are Theorem E

The freedom to pass to `S_-^(n+1) -> S_-^n` summands, with `n` arbitrary, is already
`ternary-anti-central-unit-class-is-nonpositive`. It is equivalent to the corner equation by
`twisted-leavitt-corner-fullness-equals-absence-of-k0-states`. Nothing new.

### 1.5 Halving the anti-central idempotent by group conjugates is impossible

- **An exact relation in G_3.** Put `k = s0 t0 - s1 t1` and `g = s1 t0 + s0 t1`. Then `k^2 = 1` and
  `g k g^-1 = zk`, with `z = -1` central. So `p = eps_-(1+k)/2` is an idempotent of `S_-`, and exactly
  `g p g^-1 = eps_- - p`.
- **The halving certificate.** Any state then has `s(p) = 1/2`. A halving `p = p_1 + p_2` with orthogonal
  `p_i ~ p` would force `s(p) = 2 s(p)`, so no state could exist.
- **Group conjugates cannot do it.** Suppose the `p_i = eps_-(1+k_i)/2` are conjugates of `p` by group
  elements. The sum condition becomes `eps_-(1 + k_1 + k_2 - k) = 0`: the element must be `z`-invariant.
  - The identity has coefficient 1 on the left.
  - On the right it would need `z k_i = 1` or `zk = 1`.
  - But `k` and its conjugates are not central, while `z` is.
- **So a halving must use non-monomial equivalences.** That is the corner equation again. Induced
  rank from finite subgroups blocks every monomial certificate built from finite-subgroup idempotents in
  the same way.
