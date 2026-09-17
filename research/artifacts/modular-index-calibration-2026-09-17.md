# Index = modular imbalance: calibration on the end-fixing tree (lane (c), swarm-0917)

Agent `a-gs-modular-index`, 2026-09-17. Lane (c) of `notes/agent-coordination-playbook-2026-09-17.md`, Section 11.
Script: `experiments/modular-index-calibration-2026-09-17/tree_transport.py`, output `tree_transport.out` next to it.

**Question.** On the end-fixing tree the random-order decoder transport of the strict automaton has ratio `2`, the
modular function (`injective-ca-random-order-transport-identity`, calibration). Is `2` an invariant of strictness
(a Jones index, or a Radon-Nikodym cocycle of the endomorphism the automaton induces)? If so, the route "strictness
forces a nontrivial modular cocycle; groups force it trivial" would be a new decomposition of
`gottschalk-surjunctivity-conjecture`.

**Verdict.** No. The `2` is the modular function of the host averaged over where the decoder reads. It is not an
invariant of the automaton, and every version of the index tested dies at the same step: *strictness must force
the cocycle to be nontrivial* (step P1 below). After the modular correction, the strictness signal on the tree sits
entirely in the domination inequality, which is the existing hole `injective-ca-random-order-transport-is-dominated`.

## 0. Setup and notation

- `T` is the 3-regular tree, `xi` an end, `V` its vertex set, `p(v)` the parent toward `xi`, `c, c'` the two children
  of a vertex, `Gamma = Aut(T, xi)`, `K = Gamma_o` for a root `o`.
- **Types.** For `u, w in V` let `m` be the meet of the rays from `u` and `w` to `xi`. Put `a = d(u, m)`,
  `b = d(m, w)`. Call `(a, b)` the type of `u -> w`. Then `w -> u` has type `(b, a)`, and `h(w) - h(u) = a - b`, where
  `h` is the Busemann height toward `xi` (parents are higher).
- `N(a, b)` is the number of `w` of type `(a, b)` from `o`: `N(a, 0) = 1`, `N(0, b) = 2^b`, `N(a, b) = 2^(b-1)` for
  `a, b >= 1`. In every case `N(a, b) / N(b, a) = 2^(b - a)`.
- Automata: `kappa : A_in^V -> B^V`, `Gamma`-equivariant, local. A decoder is an equivariant local map `delta` with
  `delta(kappa(x))(u) = x(u)`, reading the outputs on a finite `K`-invariant set `D(u)` (so `D(gu) = g D(u)`).
- `x` is uniform i.i.d., `y = kappa(x)`, `U` i.i.d. uniform order labels on `V`. For `w in D(u)`:

      t(u, w) = I( x(u) ; y(w) | y(D(u) ∩ past(w)), U ).

  `out(o) = sum_(w in D(o)) t(o, w)` and `in(o) = sum_(u : o in D(u)) t(u, o)`.

## 1. The modular mass-transport principle on `Aut(T, xi)`

**Proposition 1.** Let `F : V x V -> [0, inf]` be invariant under the diagonal action of `Gamma`. Then

    sum_w F(o, w) = sum_u F(u, o) 2^(b - a),      (a, b) = type of u -> o.

*Proof.* The type is a complete invariant of `Gamma`-orbits on pairs. `Gamma` is transitive on `V`. `K` is transitive
on the vertices of each type from `o`: those are `a_a(o)` when `b = 0`; the depth-`b` descendants of `o` when `a = 0`;
and for `a, b >= 1` the depth-`b` descendants of the child of `a_a(o)` not containing `o`, where `a_a(o)` is the
ancestor at height `a`. Automorphisms fixing every ancestor of `o` permute each of these sets transitively. So `F` is
a constant `c(a, b)` on pairs of type `(a, b)`. The left side is `sum_(a,b) N(a, b) c(a, b)`. The `u` with `u -> o` of
type `(a, b)` are the `u` with `o -> u` of type `(b, a)`, so there are `N(b, a)` of them, and the right side is
`sum_(a,b) N(b, a) c(a, b) 2^(b-a) = sum_(a,b) N(a, b) c(a, b)`. ∎

The same proof applies verbatim to `F(u, w) = E_lambda phi(x, U; u, w)` for any `Gamma`-invariant law `lambda` and
any equivariant measurable `phi >= 0`. In groupoid language: the rooted-configuration groupoid of `Gamma ↷ (A^V,
lambda)` (move the root along `V`) has Radon-Nikodym cocycle

    D(u -> o) = 2^(b - a) = 2^(h(u) - h(o)),

for **every** invariant probability `lambda` — the uniform measure `mu`, the image `tau_* mu` of a strict automaton,
and the image of every bijective one. For a group acting on itself every type has one element and `D = 1` for every
`lambda`.

## 2. The weighted transport identity holds on the tree for every injective automaton

**Proposition 2.** For every equivariant injective `kappa` on `A_in^V` with an equivariant finite decoder,

    out(o) = log |A_in|     and     sum_(u : o in D(u)) t(u, o) 2^(b-a) = log |A_in| .

*Proof.* `x(o)` is a function of `y(D(o))` and is independent of `U`, so `log |A_in| = I(x(o); y(D(o)) | U)`. The chain
rule along the random order of `D(o)` gives `out(o)`. `t` is diagonally invariant because `x` and `U` are i.i.d. and
`kappa`, `delta` are equivariant, so Proposition 1 applies. ∎

**Corollary 3 (what the ratio is).** Unweighted,

    in(o) / out(o) = sum_(w in D(o)) t(o, w) 2^(h(w) - h(o)) / sum_(w in D(o)) t(o, w) ,

the transport-weighted mean of the modular function along the decoder arrows `o -> w`. It depends on the orientation
of the decoder memory, not on strictness. It equals `1/2` exactly when all transport goes to children.

## 3. Exact numbers (by hand; the script recomputes every term by enumeration)

Logs to base `q`; `A = Z/q`.

| automaton | strict? | `out` | `in` (unweighted) | weighted `in` | `out/in` | `H(y(o))` | unweighted domination | weighted domination |
|---|---|---|---|---|---|---|---|---|
| `tau(x)(v) = x(p v)`, decoder `min` over children | yes | 1 | 1/2 | 1 | **2** | 1 | holds | holds (equality) |
| identity | no | 1 | 1 | 1 | 1 | 1 | holds | holds |
| shear up `(x1(v), x2(v) + x1(p v))` | no, bijective | 2 | 5/2 | 2 | **4/5** | 2 | **fails** | holds |
| shear down `(x1(v), x2(v) + x1(c) + x1(c'))` | no, bijective | 2 | 5/3 | 2 | **6/5** | 2 | holds | holds |
| `tau x shear up` on `A x A^2` | yes | 3 | 3 | 3 | **1** | 3 | holds (equality) | holds (equality) |
| `kappa` of `finite-left-inverse-identity-does-not-force-balance`, `q = 2` (bits) | injective, skewed | 2 | 3/2 | 2 | 4/3 | 1.9056 | holds | **fails** |

Derivations.

- **`tau`.** `D(u) = {c, c'}`; `y(c)` reveals `x(u)` unless `y(c')` is already past: `t(u, c) = (1/2)`. `o` is read only
  by `p(o)`, type `(0, 1)`, weight `2`.
- **Shear up.** `D(u) = {u, p(u)}`. `y(p(u))` is independent of `x(u)` and reveals `x1(p u)`, which unmasks `x2(u)` in
  `y(u)`. So `t(u, u) = 1 + P(p(u) ≺ u) = 3/2` and `t(u, p u) = P(u ≺ p u) = 1/2`. `o` is read by itself and by its two
  children, type `(1, 0)`, weight `1/2`: `in = 3/2 + 2 (1/2) = 5/2`, weighted `3/2 + 1/2 = 2`. `y(o)` is uniform on
  `A^2`, so `in = 5/2 > 2 = H(y(o))`.
- **Shear down.** `D(u) = {u, c, c'}`. `y(u)` gives `x1(u)` always and `x2(u)` iff both children are past (prob `1/3`):
  `t(u, u) = 4/3`. `y(c)` completes `x2(u)` iff `u, c'` are past (prob `1/3`): `t(u, c) = 1/3`. `o` is read by itself
  and by `p(o)` (weight `2`): `in = 5/3`, weighted `2`.
- **Product.** The components are independent and the random order restricted to each component's memory is again
  uniform, so transports add: `out = 1 + 2`, `in = 1/2 + 5/2 = 3`. The product is strict because its first
  component is.
- **`kappa`.** `D(u) = {u, c, c'}`. `y(u) = (x0(u), z(u))` with `z(u)` a function of `x0(u), x0(u'), x1(p u)`, the last
  two independent of `x(u), y(c), y(c')`. So `t(u, u) = H(x0(u)) = log q`, and by the chain rule and the sibling
  symmetry `t(u, c) = t(u, c') = (1/2) log q`. The site law gives mass `2q^-2 - q^-3` to `(1, 0)`, so
  `H(y(o)) < 2 log q` for every `q >= 2`, while the weighted in-mass is `2 log q`.

## 4. The operator-algebra forms of the index

- **Pullback of the strict automaton.** `tau(A^V)` is closed, invariant and misses the sibling-pair cylinder, which has
  infinitely many disjoint translates, so `mu(tau A^V) = 0`. Since `tau^-1(tau A^V) = A^V`, `f -> f o tau` is not
  defined on `L^inf(A^V, mu)`: it is not normal (same phenomenon as
  `complex-lamplighter-linearizations-are-normal-iff-surjective`). `tau_* mu` is singular to `mu`, so there is no
  Radon-Nikodym derivative, let alone the constant `2`.
- **Pullback of a left inverse.** For `q = 3` the decoder `sigma(y)(w) = 2 (y(c) + y(c')) mod 3` is symmetric,
  decodes `tau` (`4a = a`) and pushes `mu` to `mu` (each fibre of `(a, b) -> 2(a + b)` has 3 points). So `sigma^*` is a
  `mu`-preserving injective endomorphism of `L^inf(A^V, mu)`, and it commutes with the root-moving groupoid. Its image
  has **infinite** Pimsner-Popa index: conditioned on `sigma(y)`, the pairs `(y(c), y(c'))` are independent and uniform
  on 3 points each, so a cylinder fixing `n` such pairs has conditional expectation `3^-n` times its indicator. For even
  `q` no symmetric two-child decoder is balanced (`f(a, a) = a` makes every fibre odd), so `sigma_* mu` is a product of
  non-uniform marginals and singular to `mu` (Kakutani).
- **Where index 2 lives.** The only finite-index object is on the site algebra: `iota(f) = f o p` embeds `l^inf(V)` onto
  the functions constant on sibling pairs, with equivariant expectation `E f(v) = (f(v) + f(v'))/2` and Watatani index
  `2 = [K : c^-1 K c] = Delta(c)`. It exists only because `p` is a 2-to-1 equivariant site map. Over a group every
  equivariant site map is a bijection, and a strict automaton reads at least two sites essentially
  (`site-pullbacks-strict-iff-stabilizer-self-compressed`). So this index is `1` on every group for every automaton.

## 5. The obstruction: every member of the class dies at P1

The lane's route has two prerequisites:

- **P1.** A strict injective automaton forces a nontrivial modular cocycle / index `!= 1` on an associated measured
  groupoid.
- **P2.** Groups (unimodular) force that cocycle trivial.

P2 holds for each candidate below. Each one dies at P1, and the invariant that kills it is the modular function
`Delta = 2^(h(u) - h(o))` on the tree, which the index merely records:

1. **Cocycles of the host groupoid** (the Radon-Nikodym cocycle of the rooted-configuration groupoid, and any
   invariant of `(host, invariant measure class)`). By Proposition 1 it is `Delta` for every invariant measure on the
   tree, and `1` for every measure on a group. It does not depend on the automaton. On groups P1 therefore says "no
   strict automaton exists", which is the conclusion (compare `measure-conjugacy-invariants-cannot-certify-surjectivity`).
2. **Unweighted transport ratio.** Not an index: bijective automata give `4/5` and `6/5`, and the strict automaton
   `tau x shear up` gives exactly `1`. P1 is false on the calibration host itself.
3. **Delta-weighted transport ratio.** Identically `1` on the tree for every injective automaton (Proposition 2) and on
   every group (the identity). P1 is false.
4. **Jones / Pimsner-Popa index of the induced endomorphism.** The pullback of the automaton is not normal; the pullback
   of a balanced left inverse has infinite index; the index-2 inclusion lives on `l^inf(V)`, requires a 2-to-1 site map,
   and is `1` over groups for every automaton. P1 is false for groups-in-disguise and vacuous otherwise.

**What survives.** With the modular correction the tree's strictness is paid for exactly where it must be on a group:
weighted domination `sum_u t(u, o) 2^(b-a) <= H(y(o))` fails at `kappa`, while the weighted identity holds. So the
lane collapses into `injective-ca-random-order-transport-is-dominated`, with a sharper calibration: a proof of
domination that uses only equivariance, the chain rule and Shannon inequalities, finite decoder memory, and mass
transport *in its modular form* is valid on `Aut(T, xi) ↷ V` and is refuted by `kappa`. So a proof must use
`Delta = 1` (or freeness of the index action) **inside the domination step**, not only in the identity. This corrects
the reading "a strict automaton off groups is paid for by imbalance, not by violating domination": that holds for the
unweighted bookkeeping, in which the tree also violates domination for a *bijective* automaton (shear up).

## 6. Side idea (posted as a spark, not pursued)

The honest reframing of lane (c) is a **strengthening**, not a decomposition: *every closed unimodular group acting
transitively with compact open stabilizers on a countable set `V` is surjunctive on `A^V`*. It contains the goal
(`V = G`). Site-pullback strictness is impossible there (`c^-1 K c <= K` forces equality by Haar measure), and the
transport identity holds unweighted. When the host contains a group acting freely with finitely many orbits it reduces
to the goal for that group; hosts without such a subgroup are new calibration worlds, and a strict automaton on one
would separate "unimodular" from "group".
