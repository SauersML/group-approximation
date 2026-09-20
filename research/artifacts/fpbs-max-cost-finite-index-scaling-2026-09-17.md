# Finite-index scaling of maximal cost is one coset product

2026-09-17 (swarm-0917, transplanter, logic-computability family).
This is a written deduction over imported results already in the graph.
No priority is claimed.

## 0. Setting and notation

- `Gamma` is an infinite finitely generated group. `H <= Gamma` has finite
  index `q >= 2`.
- `b_Gamma` is a nontrivial Bernoulli shift `(A^Gamma, alpha^Gamma)` with the
  left shift `(gamma x)(g) = x(gamma^{-1} g)`.
- `C^*(G)` is the supremum of the costs of free p.m.p. `G`-actions.
- `Y = b_Gamma x Gamma/H` is the diagonal action, with uniform measure on the
  `q` cosets.
- The imports are:
  - [BM] `fpbs-bernoulli-maximal-cost`: for infinite f.g. `G`, the value
    `C^*(G)` is attained by a nontrivial Bernoulli action.
  - [AW] `abert-weiss-free-actions-weakly-contain-bernoulli`: every free
    action weakly contains every Bernoulli action, whatever the base.
  - [K] `cost-is-constant-on-weak-equivalence-classes`: for f.g. `G` and free
    actions, `b ≺ a` implies `C(a) <= C(b)`.
  - [IND] `fpbs-normalized-cost-induction-input` (Gaboriau, Proposition
    2.33): for a complete section `A`,
    `C(R) - 1 = mu(A) (C(R|A, normalized) - 1)`.
  - [STAR] `fpbs-finite-index-star-relative-cost`: a finite-index
    subrelation `S` of an aperiodic relation `T` has zero relative cost, so
    `C(T) <= C(S)`.
  - [GAB] `fpbs-gaboriau-l2-betti-normal-subgroup-and-finite-index`:
    `beta_1(H) = q beta_1(Gamma)`.

## 1. Every Bernoulli shift of G has cost C^*(G)

Let `G` be infinite and f.g., and let `beta` be any nontrivial Bernoulli
shift of `G`.

- `beta` is free.
- By [BM], some nontrivial Bernoulli shift `beta'` has `C(beta') = C^*(G)`.
- By [AW], both `beta ≺ beta'` and `beta' ≺ beta` hold, since both are free.
- By [K], `C(beta) = C(beta') = C^*(G)`.

## 2. Bernoulli restricted to H is Bernoulli

Choose `T` with `Gamma = disjoint union over t in T of H t`, so `|T| = q`.
Define `Phi(x)(h) = (x(h t))_{t in T}`, a map `A^Gamma -> (A^T)^H`.

- `Phi` is a measure-preserving isomorphism of product spaces. It is a
  relabelling of coordinates, because `(h,t) -> h t` is a bijection
  `H x T -> Gamma`.
- For `h'` in `H`, `Phi(h' x)(h) = (x(h'^{-1} h t))_t = Phi(x)(h'^{-1} h)`.
  So `Phi` intertwines `b_Gamma|H` with the left `H`-shift over the base
  `(A^T, alpha^T)`.
- `H` is infinite and finitely generated, having finite index in `Gamma`.

By Section 1, `C(b_Gamma|H) = C^*(H)`.

## 3. The coset product induces to the restriction

`Y = b_Gamma x Gamma/H` acts by `gamma (x, gH) = (gamma x, gamma g H)`. It is
free, because its first coordinate is free.

Let `A = A^Gamma x {H}`.

- **Measure.** `mu_Y(A) = 1/q`.
- **Complete.** `A` meets every orbit, since `g^{-1} (x, gH) = (g^{-1} x, H)`.
- **Restricted relation.** `(x, H)` and `gamma (x, H)` both lie in `A` iff
  `gamma H = H`, that is, iff `gamma` lies in `H`. So `(x, H) -> x`
  identifies `R_Y|A` with normalized measure with the orbit relation of
  `b_Gamma|H`.

By [IND] and Section 2,

    C(Y) - 1 = (C(b_Gamma|H) - 1)/q = (C^*(H) - 1)/q.            (3.1)

## 4. Theorem

Let `Gamma` be an infinite f.g. group and `H <= Gamma` a subgroup of index
`q`.

**(a)** `C^*(H) - 1 = q (C(b_Gamma x Gamma/H) - 1)`. This is (3.1).

**(b)** `C^*(Gamma) <= C^*(H) <= 1 + q (C^*(Gamma) - 1)`.

- *Right-hand inequality.* `Y` is a free `Gamma`-action, so
  `C(Y) <= C^*(Gamma)`. Then apply (3.1).
- *Left-hand inequality.* On `A^Gamma`, the orbit relation `S` of `b_Gamma|H`
  is a subrelation of the orbit relation `T` of `b_Gamma`.
  - Freeness makes each `T`-class the disjoint union of exactly `q`
    `S`-classes, namely `H s x` for left coset representatives `s`.
  - `T` is aperiodic.
  - So [STAR] gives `C(T) <= C(S)`, which is `C^*(Gamma) <= C^*(H)` by
    Sections 1 and 2.

**(c)** The following are equivalent:

- (i) `C^*(H) - 1 = q (C^*(Gamma) - 1)`;
- (ii) `C(b_Gamma x Gamma/H) = C(b_Gamma)`;
- (iii) `C(b_Gamma x Gamma/H) >= C(b_Gamma)`.

(i) and (ii) are equivalent by (a) and Section 1. (ii) and (iii) are
equivalent because `C(Y) <= C^*(Gamma) = C(b_Gamma)`.

So finite-index scaling of the group invariant `C^*` is exactly cost descent
through one explicit `q`-point factor map, `Y -> b_Gamma`. It is the
Bernoulli-base instance of assertion (I) in
`research/artifacts/fpbs/docs/finite-fiber-cost-descent.md`, Section 2, and
that instance is expressed entirely through group invariants.

## 5. Two routes to the full statement both force it

Write **VS(Gamma)** for "(i) holds for every finite-index `H <= Gamma`".

- **Fixed price forces VS(Gamma).** If `Gamma` has fixed price, then the free
  action `Y` has cost `C(b_Gamma)`. That is (ii).
- **The Betti target forces VS(Gamma).** Suppose `C(b_G) = 1 + beta_1(G)` for
  `G = Gamma` and `G = H`. This is the conclusion of
  `fpbs-bernoulli-cycle-tail-compactness`. Then Section 1 and [GAB] give
  `C^*(H) - 1 = beta_1(H) = q beta_1(Gamma) = q (C^*(Gamma) - 1)`.

VS(Gamma) for every infinite f.g. `Gamma` is therefore a necessary
prerequisite of `fpbs-fixed-price-universal`, restricted to f.g. groups, and
of the universal form of the cycle-tail target. It can fail on its own:

- it mentions only the `C^*` values of `Gamma` and of its finite-index
  subgroups;
- no `L^2` quantity appears in it;
- no action other than Bernoulli shifts appears in it.

## 6. What VS forces on rank gradients, with no L2 input

Import [AN], `fpbs-abert-nikolov-rank-gradient-equals-profinite-cost`: for
a Farber chain `(Gamma_n)`, `RG(Gamma; (Gamma_n)) = C(E) - 1`, where `E` is
the free boundary action.

Put `rho(Gamma) = inf over finite-index H of (d(H) - 1)/[Gamma:H]`.

**Corollary 6.1.** If VS(Gamma) holds and `Gamma` is residually finite,
then every Farber chain satisfies

    RG(Gamma; (Gamma_n)) = C^*(Gamma) - 1 = rho(Gamma).

In particular:

- the rank gradient does not depend on the Farber chain;
- it is the infimum over *all* finite-index subgroups, not only over the
  members of chains;
- every Farber boundary action has maximal cost.

*Proof.*

- Every free `H`-action is generated by `d(H)` automorphisms, so
  `C^*(H) <= d(H)`.
- VS then gives `C^*(Gamma) - 1 = (C^*(H) - 1)/[Gamma:H] <= (d(H) - 1)/[Gamma:H]`
  for every finite-index `H`. So `C^*(Gamma) - 1 <= rho(Gamma)`.
- Each term of a Farber chain is at least `rho(Gamma)`, so
  `rho(Gamma) <= RG(Gamma; (Gamma_n))`.
- By [AN], the rank gradient is `C(E) - 1`. Since `E` is free,
  `C(E) - 1 <= C^*(Gamma) - 1`.
- So `rho <= RG <= C^* - 1 <= rho`. QED.

This is distinct from `fpbs-cycle-tails-force-rank-gradient-equals-l2-betti`.
That claim needs the equality `C(b) = 1 + beta_1` and pins `RG` to `beta_1`.
Corollary 6.1 needs only VS, which is weaker than both the Betti target and
fixed price. It still gives chain-independence, the question Abért and
Nikolov left open.

**Contrapositive: a finite-model test for VS.** Suppose some residually
finite `Gamma` has two Farber chains with different rank gradients, or one
Farber chain with `RG > rho(Gamma)`. Then VS(Gamma) fails, and so do both
routes to the full statement.

## 7. Calibration on Burnside groups

Let `Gamma = B(2,n)` for large odd `n`, and let `K = ker(pi)` for
`pi : Gamma -> Z/n`, with `pi(a) = 1` and `pi(b) = 0`.

- Import `fpbs-burnside-common-upper-cost`: `C^*(K) = C^*(Gamma) = c_n`.
- Then (i) for `K` reads `c_n - 1 = n (c_n - 1)`, that is, `c_n = 1`.
- Since every free action of an infinite group costs at least 1 [BM], the
  condition `c_n = 1` is fixed price one for `Gamma`.

So VS(B(2,n)) is equivalent to fixed price one for `B(2,n)`, which is the
open hole `fpbs-burnside-upper-cost-one`. This recovers
`fpbs-burnside-explicit-action-pair` as the special case `H = K` of Section 4.

Consequently VS is not a soft consequence of weak-containment bookkeeping. A
proof of VS for all f.g. groups would in particular prove that Burnside
groups have fixed price one.

## 8. Where the weak-containment method dies (remark, not part of the claim)

The only general tool that lower-bounds the cost of one free action by the
cost of another is monotonicity [K]: if `a ≺ b_Gamma`, then
`C(a) >= C(b_Gamma)`. For (iii) one would need `Y ≺ b_Gamma`.

- For nonamenable `Gamma` and `q >= 2` this fails.
- `Gamma/H` is a factor of `Y`, so `Y ≺ b_Gamma` would give
  `Gamma/H ≺ b_Gamma`.
- Unwinding weak containment on the partition `{gH}` produces sets
  `B^n` in `b_Gamma` with two properties:
  - `mu(h B^n Δ B^n) -> 0` for every `h` in `H`;
  - `mu(B^n) -> 1/q`.
- That is a non-trivial asymptotically invariant sequence for `b_Gamma|H`.
- But `b_Gamma|H` is a Bernoulli shift of the nonamenable group `H` by
  Section 2, and such shifts are strongly ergodic (Schmidt; Jones–Schmidt).

These two strong-ergodicity citations are not imported into the graph.
Without them, this section is a pointer only.

- **Invariant that kills the class.** Every method that transports Bernoulli
  lower bounds along weak containment dies because it cannot see the finite
  factor `Gamma/H`.
- **Step where it dies.** The exact step is the passage from `Y` to `b_Gamma`.

For amenable `Gamma` everything costs 1, and VS is trivial.

## 9. The measure-equivalence form (OPEN, sketch only)

The general statement that VS serves is **ME scaling of maximal cost**.

- **Statement.** If `Gamma` and `Delta` are ME with coupling index `iota`,
  then `C^*(Gamma) - 1 = iota (C^*(Delta) - 1)`.
- **Why it is necessary.** Gaboriau's ME-invariance of fixed price makes it
  necessary for `fpbs-fixed-price-universal`.
- **Relation to VS.** VS is the case of the coupling `Omega = Gamma`,
  acted on by `Gamma x H`.

**Sketch of the reduction.** This sketch is not verified here.

- Twist the coupling by a free `Delta`-action `a''`.
- This yields a free `Gamma`-action that is SOE, with index `iota`, to
  `c x a''`. Here `c` is the coupling action of `Delta` on `Gamma\Omega`.
- With `a'' = b_Delta`, ME scaling of `C^*` follows from
  `C(c x b_Delta) >= C(b_Delta)` for both coupling actions, run in both
  directions.
- That inequality is a product-with-Bernoulli cost descent, and fixed price
  of `Delta` implies it.
- For `Omega = Gamma` the coupling action is `c = Gamma/H`, and this is
  exactly (iii).

This section is recorded as an open decomposition. It is not established.
