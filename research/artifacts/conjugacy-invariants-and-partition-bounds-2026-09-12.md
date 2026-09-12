# Conjugacy invariants are inert for Gottschalk; partition-bounded invariants are dominated by Rokhlin entropy

Lane `gk-p-bernoulli-ergodic`, 2026-09-12. Supports the Cairn claims
`measure-conjugacy-invariants-cannot-certify-surjectivity` and
`rokhlin-entropy-is-the-largest-partition-bounded-invariant`.

The question for this lane: which invariants, valid over every group, could separate the image
measure `nu = tau_* mu` of a strict injective automaton from the uniform Bernoulli measure `mu`,
and so contradict strictness?

Both results below are elementary. Their use is to classify proof architectures:
- every argument that compares an isomorphism invariant of the image measure with that of `mu` is
  void;
- every argument built on an invariant bounded by the Shannon entropy of generating partitions
  has, as its lower-bound step, Bernoulli Rokhlin maximality (INF);
- everything else must use coordinate-level data, listed in Section 3.

## 0. Setting

- `G` is a countable group and `A` a finite alphabet with `q = |A| >= 2`.
- `X = A^G` carries the shift `(g.x)(h) = x(g^-1 h)`, the uniform product measure `mu`, and the
  time-zero partition `P = {x(1) = a : a in A}`.
- `tau` is an injective cellular automaton with memory `M`. `sigma` is a decoder with memory `N`
  and `sigma tau = id`; one exists by compactness and Curtis–Hedlund–Lyndon.
- `Y = tau(X)` and `nu = tau_* mu`.

`tau` is strict when `Y != X`. By `injective-measure-preserving-ca-is-surjective` and
`bijective-ca-preserve-uniform-bernoulli-measure`, strictness is equivalent to `nu != mu`, and
also to `nu` not having full support.

## 1. Conjugacy invariants are inert

**Theorem 1.**
- (a) `tau : X -> Y` is a homeomorphism commuting with the shift, so the subshifts `X` and `Y`
  are topologically conjugate.
- (b) `tau` is an isomorphism of measure-preserving `G`-actions from `G ↷ (X, mu)` to
  `G ↷ (A^G, nu)`, since `nu(Y) = 1`.

*Proof.*
- (a) `tau` is continuous, injective and equivariant, and `X` is compact Hausdorff, so `tau` is a
  homeomorphism onto the closed set `Y`.
- (b) `tau` is a Borel bijection `X -> Y`, equivariant, with `tau_* mu = nu`; its inverse on `Y`
  is `sigma`, which is continuous. QED

**Corollary 1.1.** Every isomorphism invariant of measure-preserving `G`-actions takes the same
value on `G ↷ (A^G, nu)` as on `G ↷ (A^G, mu)`. This includes:
- the unitary equivalence class of the Koopman representation on `L^2_0` (its spectral data);
- ergodicity, weak mixing, mixing, mixing of all orders;
- strong ergodicity, and spectral gap of the Koopman representation;
- the weak equivalence class of the action;
- invariants of the orbit equivalence relation, such as cost and `l^2`-Betti numbers;
- the crossed product `L^infty(X) ⋊ G` with its Cartan subalgebra, and cocycle-superrigidity
  properties of the action;
- every entropy invariant: Rokhlin entropy, sofic entropy for each sofic approximation, naive
  entropy, and the f-invariant over free groups.

Likewise, every conjugacy invariant of `G`-subshifts takes the same value on `Y` and on `A^G`.

**Corollary 1.2 (form of a separating argument).** Let `S` be a property of invariant Borel
probability measures on `A^G` such that `S(mu)` holds and `S(tau_* mu)` fails for every strict
`tau`. Then `S` is not invariant under isomorphism of the actions. It must depend on how the
measure sits in the configuration space `A^G`, meaning on the coordinate partition. *Proof:* if
`S` were invariant, Theorem 1(b) would give `S(tau_* mu) = S(mu)`. QED

This is the all-groups, all-invariants form of the observation in the Attempts of
`kazhdan-bernoulli-rigidity-forces-surjective-embeddings`. There, spectral gap, strong ergodicity,
Glasner–Weiss closedness and the absence of finite quotients all hold for a strict embedding over
`R^x`, because they are invariant under the conjugacy.

## 2. Partition-bounded invariants

For an ergodic measure-preserving action `G ↷ (Z, zeta)`:
- a countable measurable partition `Q` is *generating* when the smallest `G`-invariant
  sigma-algebra containing `Q` is everything, mod null sets;
- Rokhlin entropy is `h^Rok(G ↷ Z) = inf { H_zeta(Q) : Q generating countable partition }`
  (Seward).

Call an isomorphism invariant `I` of ergodic measure-preserving `G`-actions, with values in
`[0, infty]`, *partition-bounded* when

```text
I(G ↷ (Z, zeta)) <= H_zeta(Q)      for every countable generating partition Q.
```

**Theorem 2.**
- (a) `h^Rok` is partition-bounded.
- (b) Every partition-bounded invariant `I` satisfies `I <= h^Rok` on every action.
- (c) If some partition-bounded invariant has `I(G ↷ (A^G, mu_A)) = log |A|`, then
  `h^Rok(G ↷ (A^G, mu_A)) = log |A|`.

So Rokhlin entropy is the largest partition-bounded invariant.

*Proof.*
- (a) `h^Rok <= H(Q)` for each generating `Q` by definition. `h^Rok` is an isomorphism invariant,
  because an isomorphism carries generating partitions to generating partitions and preserves
  Shannon entropy.
- (b) Take the infimum of `I <= H(Q)` over generating `Q`.
- (c) `log |A| = I <= h^Rok <= H_mu(P) = log |A|`, where `P` is the generating time-zero
  partition. QED

**Examples of partition-bounded invariants.**
- *Sofic entropy for a fixed sofic approximation.* It is bounded by the Shannon entropy of any
  generating partition, so Theorem 2(b) recovers `h^Sigma <= h^Rok` wherever `h^Sigma` is defined.
- *The f-invariant over a free group of rank `r`.* `F(Q) = (1-2r) H(Q) + sum_i H(Q ∨ s_i Q)` is at
  most `H(Q)`, because `H(Q ∨ s_i Q) <= 2 H(Q)`.

These are standard remarks and nothing depends on them.

**Corollary 2.1 (entropy architectures reduce to INF).** Every proof of surjunctivity of `G` of the
following form needs, at its lower-bound step, `h^Rok((A^k)^G, uniform) = k log |A|` for the
relevant `k`:
1. a lower bound `I((A^k)^G, uniform) >= k log |A|` for a partition-bounded invariant `I`;
2. a conversion of strictness into generating partitions of amplified Bernoulli shifts with
   Shannon entropy below that bound.

That is Bernoulli Rokhlin maximality, `bernoulli-rokhlin-entropy-maximal-for-every-group` on that
group. Step 2 is already supplied for Rokhlin entropy by
`strict-automaton-lowers-bernoulli-rokhlin-entropy`. So no partition-bounded invariant other than
Rokhlin entropy offers an easier route; the lower bound is the whole difficulty.

Step 2 cannot be a comparison of `I(nu)` with `I(mu)`: Corollary 1.1 makes them equal. The deficit
must be produced at the level of partitions, which is data of type D1 below.

## 3. The non-invariant data a proof must use

By Corollary 1.2, a proof of surjectivity must use data that is not an isomorphism invariant of
the image action.

- **D1. Window laws of the coordinate partition.** The numbers `nu(y|F = p)`. Strictness is
  equivalent to some `nu(y|F = p) = 0`. These feed Shannon-entropy deficits `H_nu(P^F) < |F| log q`,
  and through markers and amplification they feed Rokhlin deficits.
- **D2. Specification and completion counts.** `nu` is the unique uniform Gibbs measure of the
  shift of finite type `Y`, with completion counts `N_Y(E, c) = |A|^|I_E| b_E(c)`
  (`research/artifacts/gottschalk-injective-image-uniform-gibbs-bridge-2026-09-08.md`). The
  residual boundary loss `b_E` is exactly where amenability is used in the classical proof.
- **D3. Block codes in both directions.** `nu` is finitely dependent: `y|F` and `y|F'` are
  independent when `F M` and `F' M` are disjoint. The inverse is a block code of radius `N` on
  `Y`.
- **D4. Group structure of the index set.** `end-fixing-tree-symmetries-carry-strict-automata` is
  a homogeneous space of an amenable but non-unimodular group on which D1, D2 and D3 are all
  available and a strict copying automaton exists. So D1–D3, together with invariance under an
  amenable transitive symmetry group, cannot prove surjectivity. A proof must use that the index
  set is the group acting on itself (unimodularity, mass transport, balance), or finite models.

**Items this lane was asked to consider, with verdicts:**
- *Koopman spectral measure, strong ergodicity, mixing of all orders:* isomorphism invariants,
  inert by Corollary 1.1.
- *Conditional measures on a Garden-of-Eden window:* type D2. The window's conditional law under
  `nu` is uniform over admissible completions. Proper support is visible there, but it separates
  nothing without a counting inequality that uses D4.
- *Local statistics of patterns:* type D1. They always separate `nu` from `mu` when `tau` is
  strict. The content of a proof is an inequality showing that this is impossible, not a separation.
- *Topological full support:* full support of `nu` is equivalent to surjectivity, which is a
  restatement. Topological conjugacy invariants of `Y` equal those of `A^G`. "`A^G` is conjugate to
  no proper subshift of itself" is the conjecture for `(G, A)`, not a tool.

## 4. Status

Nothing here decides the conjecture. The two theorems kill every "invariant comparison" route and
identify INF as the unavoidable lower bound of every partition-bounded invariant architecture.
Positive lanes outside those architectures must use D4 together with D1–D3. Mass transport over
unimodular groups is the natural candidate (lane `gk-p-bernoulli-mass`).
