# Weak-equivalence invariants give no lower bound for Bernoulli Rokhlin entropy

Lane `gk-p-inf-cost`, 2026-09-12. Supports the Cairn claims
`nontrivial-bernoulli-shifts-are-weakly-equivalent`,
`cost-is-constant-on-weak-equivalence-classes`,
`weak-invariants-give-no-bernoulli-rokhlin-lower-bound`, the refuted prerequisite
`weak-invariants-bound-bernoulli-rokhlin-entropy-below`, and the dead route
`positive-rokhlin-entropy-via-weak-invariant-bounds`. gk-vf-positive verified Sections 1–4
(Section 5 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`); the corrections made
after its trust notes are listed in Section 5 below.

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

**Imported theorem.** Abért–Weiss, *Bernoulli actions are weakly contained in any free action*,
arXiv:1103.1063v2, §1, read 2026-09-12 from https://arxiv.org/html/1103.1063v2. The paper defines
"Let κ be a probability space. The Bernoulli action κ^Γ is defined as the set of maps from Γ to κ,
endowed with the product measure and the shift action by Γ." It proves:

> Theorem 1: Let Γ be a countable infinite group and let f be a free p.m.p. action of Γ. Then f
> weakly contains every Bernoulli action of Γ. In particular, all free factors of i.i.d.-s of Γ are
> weakly equivalent.

**Lemma 2.1.** If `a` is free and `b_λ` is a finite-alphabet Bernoulli shift, then `b_λ ≺ a`.

*Proof.* Theorem 1 with base `κ = (k, λ)`. QED

**Proposition 2.2.** Over a countably infinite group, any two nontrivial finite-alphabet Bernoulli
shifts `b_λ` and `b_λ'` are weakly equivalent.

*Proof.* `b_λ'` is free by Lemma 1.1, so `b_λ ≺ b_λ'` by Lemma 2.1. Symmetrically
`b_λ' ≺ b_λ`. QED

**Remark 2.3 (from the finitary selector).** The repository imports Theorem 1 in a finitary form as
`fpbs-aw-finite-pattern-input`. In a free action `a = G ↷ (X, μ)`, for finite `E ⊂ G` and `η > 0`,
some Borel `ℓ: X → k` has joint label law `(ℓ(e^(-1)·x))_(e ∈ E)` within `η` of `λ^E` in total
variation. That node is worded for a Bernoulli parameter. For an arbitrary finite probability vector
`λ`, a selector of this kind gives Lemma 2.1 directly:
1. Let `F ⊂ G` be finite, `B_1, …, B_m` a Borel partition of `k^G`, and `ε > 0`. Choose a finite
   `W ⊂ G` and unions of `W`-cylinders `D_1, …, D_m` with `λ^G(B_i Δ D_i) < ε/(8m)`.
2. Disjointify: `C_i = D_i \ (D_1 ∪ … ∪ D_(i−1))` for `i < m`, and
   `C_m = k^G \ (C_1 ∪ … ∪ C_(m−1))`. These are unions of `W`-cylinders and form a partition. A point
   `x` in no `B_j Δ D_j` lies in exactly one `D_j`, the one with `x ∈ B_j`, so it lies in `B_i ∩ C_i`
   for that `i` and in no other `C_j`. So `λ^G(B_i Δ C_i) ≤ Σ_j λ^G(B_j Δ D_j) < ε/8` for every `i`.
3. Since `g` preserves `λ^G`, `|λ^G(g B_i ∩ B_j) − λ^G(g C_i ∩ C_j)| < ε/4`.
4. Take `ℓ` for `E = W ∪ F W` and `η = ε/2`. The label map `Λ: X → k^G`,
   `Λ(x)(h) = ℓ(h^(-1)·x)`, is equivariant:
   `Λ(g·x)(h) = ℓ(h^(-1) g·x) = Λ(x)(g^(-1) h) = (g·Λ(x))(h)`. Put `A_i = Λ^(-1)(C_i)`, so
   `μ(g A_i ∩ A_j) = Λ_*μ(g C_i ∩ C_j)`. The set `g C_i ∩ C_j` is determined by the coordinates in
   `gW ∪ W ⊆ E`, where `Λ_*μ` is within `η` of `λ^E`. So
   `|μ(g A_i ∩ A_j) − λ^G(g C_i ∩ C_j)| ≤ ε/2`.
5. Adding the errors, `|μ(g A_i ∩ A_j) − λ^G(g B_i ∩ B_j)| < ε`.

Once that node's statement is widened from a Bernoulli parameter to finite probability vectors, it
supports Lemma 2.1 on its own. The Cairn route imports Theorem 1 directly instead.

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
* **Cost.** Let `G` be finitely generated. Cost is monotone under weak containment of free actions,
  `b ≺ a ⇒ C(a) ≤ C(b)`. This is Kechris's theorem, quoted by Abért–Weiss (§1): "A. Kechris showed
  that for finitely generated groups and free actions, the cost is monotonic with respect to weak
  containment [7, Corollary 10.14]". So cost is constant on weak-equivalence classes
  (`cost-is-constant-on-weak-equivalence-classes`). Abért–Weiss, Theorem 9, is the groupoid-cost form.
* **ℓ²-Betti numbers.** The ℓ²-Betti numbers `β^(2)_n(G)` are group invariants. The ℓ²-Betti
  numbers of the orbit relation of a free action are the group's (Gaboriau), but Theorem 3.1 needs
  only the group invariants.

So, for finitely generated `G`, no inequality `h^Rok_G(b_λ) ≥ F(C(b_λ), β^(2)_*(G))`, valid for every
nontrivial base, has a positive right side. The same holds for every other weak-equivalence
invariant: invariants of approximate finite statistics, ultraproduct classes of the action, or the
fixed price of `G`.

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

## 5. Verification and corrections

gk-vf-positive re-derived Sections 1–4 and passed them. Changes made after its trust notes:
* **Section 2 now imports Abért–Weiss Theorem 1 verbatim, and that covers every base.** Before, Lemma 2.1
  was derived from `fpbs-aw-finite-pattern-input`, whose wording covers only a Bernoulli parameter.
  That derivation is now Remark 2.3, with the disjointification step the verifier added (constant
  `ε/(8m)`).
* **The monotonicity of cost under weak containment is Kechris's, for finitely generated groups.** The
  earlier text attributed it to Abért–Weiss Theorem 9 and omitted that hypothesis. Theorem 9 is their
  groupoid-cost extension. Every host of `bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups` is
  finitely generated, so nothing downstream changes.
* **Sources.** The Abért–Weiss quotations were read from the arXiv HTML of v2 on 2026-09-12. Reference
  [7] of that paper was not read, so the corollary number is as Abért–Weiss print it.
