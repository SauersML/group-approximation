# Weak-equivalence invariants give no lower bound for Bernoulli Rokhlin entropy

Lane `gk-p-inf-cost`, 2026-09-12. Supports the Cairn claims
`nontrivial-bernoulli-shifts-are-weakly-equivalent`,
`cost-is-constant-on-weak-equivalence-classes`,
`weak-invariants-give-no-bernoulli-rokhlin-lower-bound`, the refuted prerequisite
`weak-invariants-bound-bernoulli-rokhlin-entropy-below`, and the dead route
`positive-rokhlin-entropy-via-weak-invariant-bounds`.

The question was whether orbit-equivalence invariants that need no finite models (cost,
ℓ²-Betti numbers, weak containment, measure equivalence) can bound the Rokhlin entropy of a
Bernoulli shift from below on a nonsofic host, and so prove INF, POS or RBS there
(`seward-per-group-rokhlin-entropy-of-bernoulli-shifts`). The answer here is no, for every
invariant that is constant on weak-equivalence classes and for every group invariant. The reason
is elementary: all nontrivial Bernoulli shifts over an infinite group are weakly equivalent, while
their Rokhlin entropies go to zero with the base entropy.

## Conventions

* `G` is a countably infinite group. A p.m.p. action `a = G ↷ (X, μ)` is free when every
  `g ≠ 1` fixes a null set.
* For a finite set `k = {0, …, k−1}` with `k ≥ 2` and a probability vector `λ` on `k`, the
  Bernoulli shift is `b_λ = G ↷ (k^G, λ^G)` with `(g·x)(h) = x(g^(-1) h)`. It is *nontrivial*
  when `λ` is not a point mass.
* **Weak containment** (Kechris). `b = G ↷ (Y, ν)` is weakly contained in `a = G ↷ (X, μ)`,
  written `b ≺ a`, if for every finite `F ⊂ G`, every finite Borel partition `B_1, …, B_m` of `Y`
  and every `ε > 0` there is a Borel partition `A_1, …, A_m` of `X` with
  `|μ(g A_i ∩ A_j) − ν(g B_i ∩ B_j)| < ε` for all `g ∈ F` and all `i, j`. `a` and `b` are
  *weakly equivalent* when `a ≺ b` and `b ≺ a`.
* **Rokhlin entropy.** `h^Rok_G(X, μ)` is the infimum of the Shannon entropies `H(α)` of the
  countable Borel partitions `α` of `X` whose `G`-translates generate the Borel σ-algebra mod null
  sets.

## 1. Nontrivial Bernoulli shifts are free

**Lemma 1.1.** Every nontrivial Bernoulli shift `b_λ` over a countably infinite group is free.

*Proof.* Fix `g ≠ 1`. A point fixed by `g` satisfies `x(h) = x(g^(-1) h)` for every `h`. The pairs
`{h, g^(-1) h}` are 2-element sets, and each element of `G` lies in at most two of them. So
infinitely many pairwise disjoint pairs `{h_i, g^(-1) h_i}` exist. Their coordinates are
independent, and each equality has probability `s = Σ_j λ(j)^2 < 1`, because `λ` is not a point
mass. So the fixed set has measure at most `s^m` for every `m`, which is `0`. QED

## 2. Nontrivial Bernoulli shifts are weakly equivalent

**Imported input** (`fpbs-aw-finite-pattern-input`, Abért–Weiss, *Bernoulli actions are weakly
contained in any free action*, arXiv:1103.1063, Theorem 1). Let `a` be a free p.m.p. action of
`G`, `E ⊂ G` finite, `k ≥ 2`, `λ` a probability vector on `k` and `η > 0`. There is a Borel map
`ℓ: X → k` whose joint law of labels `(ℓ(e^(-1)·x))_(e ∈ E)` is within `η` in total variation of
`λ^E`.

**Lemma 2.1.** If `a` is free and `b_λ` is a Bernoulli shift with finite alphabet, then `b_λ ≺ a`.

*Proof.* Let `F` be finite, `B_1, …, B_m` a partition of `k^G`, and `ε > 0`.
1. Choose a finite window `W ⊂ G` and a partition `C_1, …, C_m` of `k^G` into unions of
   `W`-cylinders with `λ^G(B_i Δ C_i) < ε/4` for every `i`. This is possible because cylinder
   sets generate the product σ-algebra.
2. Since `g` preserves `λ^G`, `|λ^G(g B_i ∩ B_j) − λ^G(g C_i ∩ C_j)| < ε/2`.
3. The numbers `λ^G(g C_i ∩ C_j)` for `g ∈ F` depend only on the law of the labels on the finite
   set `E = W ∪ F W`, where they are iid with law `λ`.
4. Take `ℓ` from the imported theorem for this `E` and `η = ε/2`. Put
   `A_i = {x : (ℓ(e^(-1)·x))_(e ∈ W)` lies in the cylinder pattern set of `C_i}`. Then
   `μ(g A_i ∩ A_j)` is computed from the law of `(ℓ(e^(-1)·x))_(e ∈ E)` exactly as
   `λ^G(g C_i ∩ C_j)` is computed from `λ^E`, so the two differ by at most `η`.
5. Adding the errors gives `|μ(g A_i ∩ A_j) − λ^G(g B_i ∩ B_j)| < ε`. QED

**Proposition 2.2.** Over a countably infinite group, any two nontrivial finite-alphabet Bernoulli
shifts `b_λ` and `b_λ'` are weakly equivalent.

*Proof.* `b_λ'` is free by Lemma 1.1, so `b_λ ≺ b_λ'` by Lemma 2.1. Symmetrically
`b_λ' ≺ b_λ`. QED

## 3. Blindness

**Theorem 3.1.** Let `G` be countably infinite, and let `Φ` be a quantity attached to free p.m.p.
actions of `G` such that either
* `Φ(a) = Φ(b)` whenever `a` and `b` are weakly equivalent, or
* `Φ(a)` depends only on `G`.

Then `Φ` takes a single value `Φ_B(G)` on all nontrivial finite-alphabet Bernoulli shifts. For
every function `F` such that `h^Rok_G(k^G, λ^G) ≥ F(Φ(b_λ))` holds for all nontrivial `b_λ`,
`F(Φ_B(G)) ≤ 0`.

*Proof.* The first claim is Proposition 2.2, or trivial in the second case. The time-zero partition
`{x : x(1) = j}` generates the product σ-algebra under translation and has entropy `H(λ)`. So
`h^Rok_G(k^G, λ^G) ≤ H(λ)`. As `λ = (1−p, p)` on `{0, 1}` with `p → 0`, the shift stays nontrivial
and `H(λ) → 0`. So `F(Φ_B(G)) ≤ inf_p H(1−p, p) = 0`. QED

**Corollary 3.2 (cost and ℓ²-Betti numbers).**
* **Cost.** The cost `C(a)` of the orbit relation is monotone under weak containment, `b ≺ a ⇒
  C(a) ≤ C(b)` (`cost-is-constant-on-weak-equivalence-classes`, Abért–Weiss arXiv:1103.1063
  Theorem 9), so it is constant on weak-equivalence classes.
* **ℓ²-Betti numbers.** The ℓ²-Betti numbers `β^(2)_n(G)` are group invariants. The ℓ²-Betti
  numbers of the orbit relation of a free action are the group's (Gaboriau), but Theorem 3.1 needs
  only the group invariants.

So no inequality `h^Rok_G(b_λ) ≥ F(C(b_λ), β^(2)_*(G))`, valid for every nontrivial base, has a
positive right side. The same holds for every other weak-equivalence invariant: invariants of
approximate finite statistics, ultraproduct classes of the action, or the fixed price of `G`.

**Calibration.** Over `F_2`, every free action has cost `2` and `β^(2)_1(F_2) = 1`. Yet
`h^Rok(2^(F_2), (1−p, p)^(F_2)) = H(1−p, p) → 0`, because `F_2` is sofic. So even for a group with
positive first ℓ²-Betti number, `h^Rok ≥ C − 1` fails.

## 4. What survives, and the Kazhdan hosts

**Remark 4.1 (everything is in `h_sup`).** By Seward, Theorem 1.10
(`seward-per-group-rokhlin-entropy-of-bernoulli-shifts`),
`h^Rok_G(L^G, λ^G) = min{H(L, λ), h_sup(G)}`. So a lower bound for a Bernoulli shift is a lower
bound for the group invariant `h_sup(G)`, and Theorem 3.1 says it must also see the base entropy.
The theorem does not exclude an inequality `h_sup(G) ≥ c(G)` through a group invariant `c`. Any
finite such bound proves only POS(G), the existence of one action of positive entropy. On hosts
with centralized self-copies POS and INF coincide
(`rokhlin-supremum-dichotomy-with-centralized-self-copies`).

**Remark 4.2 (first-order cost invariants vanish on Kazhdan hosts).** Let `G` be countably infinite
with property (T).
1. The infimum of the costs of its free actions is `1` (`fpbs-kazhdan-groups-have-cost-one`,
   Hutchcroft–Pete arXiv:1810.11015).
2. Gaboriau's inequality `β^(2)_1(G) ≤ C(a) − 1` for every free action `a`
   (`fpbs-amen2-betti-cost-input`) then gives `β^(2)_1(G) = 0`.
3. So every bound `h_sup(G) ≥ F(inf-cost(G) − 1, β^(2)_1(G))` with `F(0, 0) = 0` is vacuous on the
   hosts of `bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups`.

Two group-level quantities remain unconstrained by this lane:
* the maximal cost of a Kazhdan group, attained by its Bernoulli shifts
  (`fpbs-bernoulli-maximal-cost`), whose equality with `1` is the open fixed-price question;
* the higher ℓ²-Betti numbers of a simple Kazhdan host.

No inequality relating either to `h_sup` is known.

**Remark 4.3 (orbit equivalence on rigid hosts).** Suppose a host's Bernoulli shifts are orbit
equivalence superrigid in Popa's sense (infinite groups with property (T) are among Popa's w-rigid
groups). Then an orbit equivalence between two of its Bernoulli shifts comes from a conjugacy up to
an automorphism of `G`. So on such hosts orbit-equivalence invariants of Bernoulli shifts are
conjugacy invariants, and an OE-invariant lower bound is no easier than a lower bound for Rokhlin
entropy itself. This is only a no-reduction remark. The cocycle-superrigidity mechanism is the lane
`gk-p-bernoulli-popa`, and nothing here depends on it.
