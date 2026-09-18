# The excess over the Rokhlin supremum never drops under Bernoulli transfers (2026-09-17)

Agent: swarm-0917-w4-gs-rokhlin-threshold (role inverter, family minimal-counterexample).
Target hole: `bernoulli-rigidity-threshold-equals-rokhlin-supremum` (H2). Result node:
`rokhlin-excess-never-drops-under-bernoulli-transfers`.

## 0. Setting and notation

- Groups are countably infinite. `s(G) = h^Rok_sup(G) ∈ [0, ∞]`.
- For an ergodic p.m.p. action, `h^Rok_G(X) = inf { H(α) : α a countable measurable partition whose
  `G`-translates generate the σ-algebra mod null sets }` (Seward, arXiv:1501.03367v4, Definition in §1).
- `X_h^G` is the Bernoulli shift over `G` with base entropy `h`; well defined for finite `h`
  (`bernoulli-shifts-with-equal-base-entropy-are-isomorphic`).
- `a ~_G b` iff `X_a^G ≅ X_b^G` (for `a, b ∈ (0, ∞)`). A pair with `a ≠ b` is *nontrivial*.
- `R(G)` = non-rigid levels, `r(G) = inf R(G)` (`bernoulli-collapse-is-null-or-eventually-total`).
- **Excess** of a nontrivial pair `(a, b)` over `G` with `s(G) < ∞`: `e = min(a, b) − s(G)`. By the threshold
  (item 6 of `bernoulli-isomorphism-collapse-set-is-a-subgroup`), every true nontrivial pair has `s(G) < ∞` and
  `e ≥ 0`.

Imported facts (all ESTABLISHED in the graph):

- **(F1) Products.** `a ~_G b ⇒ a + t ~_G b + t` for `t ≥ 0` (item 1 of the subgroup node).
- **(F2) Co-induction.** `G ≤ Γ`, `a ~_G b ⇒ a ~_Γ b` (item 7 there; proof (d) of
  `bernoulli-entropy-counterexample-constraints`).
- **(F3) Restriction.** `H ≤ G` of index `k`, `a ~_G b ⇒ ka ~_H kb` (same two sources).
- **(F4) Threshold.** A nontrivial pair over `G` has `min(a, b) ≥ s(G)` (item 6).
- **(F5) Seward's formula.** For finite `H(L)`, `h^Rok_G(L^G) = min(H(L), s(G))`
  (`seward-per-group-rokhlin-entropy-of-bernoulli-shifts`, item 1).
- **(F6) Upward closure.** `R(G)` is upward closed and contained in `[s(G), ∞)`
  (`bernoulli-collapse-is-null-or-eventually-total`, item 3).

## 1. Two supremum inequalities

**Lemma 1.1 (overgroups).** If `G ≤ Γ` and `s(G) < ∞`, then `s(Γ) ≤ s(G)`.

*Proof.* Let `(L, λ)` be a finite-entropy base with `H(L) > s(G)`, and `X = L^Γ`. Let `π: X → L^G` be the
restriction of a configuration to `G`; it is a `G`-equivariant factor onto the `G`-Bernoulli shift with base `L`.
By (F5) over `G`, for `ε > 0` there is a partition `β` of `L^G` with `H(β) < s(G) + ε` whose `G`-translates
generate `L^G`. In particular the coordinate partition `ξ_e` of `L^G` at `e` is measurable, mod null sets, with
respect to `σ(G·β)`. Pull back: `π^{-1}β` is a partition of `X` of the same entropy, and `σ(Γ·π^{-1}β)` contains
`σ(G·π^{-1}β) ⊇ π^{-1}ξ_e`, the `Γ`-coordinate at `e`. The `Γ`-translates of that coordinate generate `X`, so
`π^{-1}β` is `Γ`-generating. The Bernoulli shift `X` is ergodic, so `h^Rok_Γ(X) ≤ s(G) + ε`. By (F5) over `Γ`,
`min(H(L), s(Γ)) ≤ s(G)`. Since `H(L) > s(G)`, this forces `s(Γ) ≤ s(G)`. ∎

**Lemma 1.2 (finite index).** If `H ≤ G` has index `k` and `s(G) < ∞`, then `s(G) ≤ s(H) ≤ k·s(G)`.

*Proof.* The left inequality is Lemma 1.1. For the right, take `H(L) > s(G)`, `X = L^G`, and right cosets
`G = ⊔_{j ≤ k} H s_j`. By (F5), pick a `G`-generating `α` with `H(α) < s(G) + ε`, and put
`α' = ∨_j s_j·α`, with `H(α') ≤ k(s(G) + ε)`. Every `g ∈ G` is `h s_j`, so `g·α = h·(s_j·α)` is refined by
`h·α'`. Hence `σ(H·α') ⊇ σ(G·α)`, and `α'` is `H`-generating. Restricted to `H`, `X` is the `H`-Bernoulli shift
with base `L^k` (proof (d) of `bernoulli-entropy-counterexample-constraints`), which is ergodic, of base entropy
`k H(L) > k s(G)`. By (F5) over `H`, `min(k H(L), s(H)) ≤ k s(G) + kε`. Letting `ε → 0` and using
`k H(L) > k s(G)` gives `s(H) ≤ k s(G)`. ∎

## 2. The transfer calculus and the excess floor

**Definition 2.1 (transfer calculus).** A *level family* `≈ = (≈_G)` assigns to each countably infinite group an
equivalence relation on `(0, ∞)`. Given a set `S` of *seeds* `(G, a, b)`, `T(S)` is the smallest level family
containing every seed (`a ≈_G b`) and closed under:
- **(T-prod)** `a ≈_G b ⇒ a + t ≈_G b + t` for `t ≥ 0`;
- **(T-co)** `G ≤ Γ`, `a ≈_G b ⇒ a ≈_Γ b`;
- **(T-res)** `H ≤ G` of index `k`, `a ≈_G b ⇒ ka ≈_H kb`;
- equivalence closure within each group.

(Groups are taken up to isomorphism; `≤` means an injective homomorphism.) By (F1)–(F3) and Seward's
equal-entropy theorem, if every seed is a true isomorphism then `T(S) ⊆ ~`. Every construction of Bernoulli
isomorphisms recorded in the graph so far that moves between groups or levels is a step of `T`.

**Definition 2.2 (paths and defect).** A *path* `p` from `G` to `Γ` is a finite sequence of steps, each either
`co: G_i ≤ G_{i+1}` or `res: G_{i+1} ≤ G_i` of finite index `k_i`. For `e ≥ 0` define `E(p, e)` recursively:
`E(∅, e) = e`; a `co` step sends `E ↦ E + s(G_i) − s(G_{i+1})`; a `res` step sends
`E ↦ k_i E + k_i s(G_i) − s(G_{i+1})`. Only groups with finite supremum occur (Lemmas 1.1–1.2 keep it finite).
The *defect* of a step is the added constant `s(G_i) − s(G_{i+1})`, respectively `k_i s(G_i) − s(G_{i+1})`. Both
are `≥ 0` by Lemmas 1.1 and 1.2, and `k_i ≥ 1`. So `E(p, e) ≥ e + Σ defects ≥ e`.

For a seed set `S` whose nontrivial seeds all satisfy (F4), put, for each `Γ` with `s(Γ) < ∞`,

    δ_S(Γ) = inf { E(p, min(a,b) − s(G)) : (G, a, b) ∈ S nontrivial, p a path from G to Γ }  ∈ [0, ∞].

**Theorem 2.3 (excess floor).** Let every nontrivial seed of `S` satisfy (F4). Then for every group `Γ` and every
nontrivial pair `a ≈_Γ b` in `T(S)`: `s(Γ) < ∞` and `min(a, b) ≥ s(Γ) + δ_S(Γ)`.

*Proof.* Define the level family `F` by: `a F_Γ b` iff `a = b`, or `s(Γ) < ∞` and
`min(a, b) ≥ s(Γ) + δ_S(Γ)`. It suffices to show that `F` contains `S` and is closed under the four operations,
since then `T(S) ⊆ F`.
- *Equivalence relation.* Reflexive and symmetric. If `a F b F c` with `a ≠ b ≠ c`, then `a, b, c ≥ s + δ`, so
  `a F c` (or `a = c`).
- *Seeds.* The empty path gives `δ_S(G) ≤ min(a, b) − s(G)`.
- *(T-prod).* `min(a + t, b + t) = min(a, b) + t`.
- *(T-co).* Let `G ≤ Γ`, `a F_G b` nontrivial. By Lemma 1.1, `s(Γ) ≤ s(G) < ∞`. Every path `p` from a seed to
  `G` extends by the step `co` to a path `p'` to `Γ` with `E(p', e) = E(p, e) + s(G) − s(Γ)`. Taking infima,
  `δ_S(Γ) ≤ δ_S(G) + s(G) − s(Γ)`. So `min(a, b) ≥ s(G) + δ_S(G) ≥ s(Γ) + δ_S(Γ)`.
- *(T-res).* Let `H ≤ G` of index `k`, `a F_G b` nontrivial. By Lemma 1.2, `s(H) ≤ k s(G) < ∞`. Extending paths
  by `res` gives `E(p', e) = k E(p, e) + k s(G) − s(H)`; infima commute with `x ↦ kx + c`, so
  `δ_S(H) ≤ k δ_S(G) + k s(G) − s(H)`. Hence `min(ka, kb) = k min(a, b) ≥ k s(G) + k δ_S(G) ≥ s(H) + δ_S(H)`. ∎

**Corollary 2.4 (the invariant).** Along every derivation in `T`, the excess `min(a, b) − s(·)` of a nontrivial
pair is bounded below by the excess of some seed plus the total defect of the path that carried it. Products add
`t ≥ 0`; co-induction adds `s(G) − s(Γ) ≥ 0`; restriction multiplies by `k ≥ 1` and adds `k s(G) − s(H) ≥ 0`;
chaining takes a minimum over its links. No step lowers it.

## 3. Consequences for the threshold claim

Write **H2(Γ)** for `bernoulli-rigidity-threshold-equals-rokhlin-supremum` at `Γ`: `s(Γ) < ∞` and
`r(Γ) = s(Γ)`. By (F6) this says: for every `ε > 0` there is a true nontrivial pair over `Γ` with
`min(a, b) < s(Γ) + ε`.

**Corollary 3.1 (class kill).** Let `S` be a set of true isomorphisms satisfying (F4), and suppose `T(S)` witnesses
H2(Γ), i.e. it contains nontrivial pairs over `Γ` with `min(a, b) − s(Γ)` arbitrarily small. Then `δ_S(Γ) = 0`.
So for every `ε > 0` there are a seed `(G, a, b) ∈ S` and a path `p` from `G` to `Γ` with
- seed excess `min(a, b) − s(G) < ε`: the seed already witnesses `r(G) < s(G) + ε`, which is H2 at `G` up to `ε`;
- every `co` step `G_i ≤ G_{i+1}` with `s(G_i) − s(G_{i+1}) < ε`;
- every `res` step `G_{i+1} ≤ G_i` of index `k_i` with `k_i s(G_i) − s(G_{i+1}) < ε`, i.e. within `ε` of
  Seward's open finite-index formula.

*Proof.* Theorem 2.3 and `E(p, e) ≥ e + Σ defects`. ∎

Where every member of the class dies:
- **Eventual-collapse seeds.** A seed "`a ≈ b` for all `a, b ≥ M`" over `G` has excess `M − s(G)`. If
  `M > s(G)` is fixed, then `δ_S ≥ M − s(G) > 0` on every host, since `E(p, e) ≥ e`. So no product, co-induction,
  restriction or chaining argument from H1 alone gives H2. This is the formal model B of
  `bernoulli-collapse-is-null-or-eventually-total`, now for the multi-group calculus and not only one group.
- **Seeds from groups of larger supremum.** If `s(G) ≥ σ` and `p` contains a `co` step to a group of supremum
  `≤ s(G) − σ`, the defect is `≥ σ`. Example: on `P × G` hosts with `s(P × G) = 0` (Seward, Theorem 1.11 of
  arXiv:1501.03367v4), seeds co-induced from `G` give only levels `≥ s(G)`.
- **Seeds with positive excess.** Any seed family whose excesses are bounded below by `c > 0` gives `δ_S ≥ c` on
  every host.

So a proof of H2(Γ) by transfers needs, as input, near-threshold isomorphisms at some group, carried along
defect-free paths. That input is H2 itself up to `ε`, at a group of the same or of exactly scaled supremum.

**Theorem 3.2 (permanence).**
1. If `G ≤ Γ` and `s(Γ) = s(G) < ∞`, then H2(G) ⇒ H2(Γ).
2. If `H ≤ G` has index `k` and `s(H) = k s(G) < ∞`, then H2(G) ⇒ H2(H).
3. If `s(G) = 0`, then H2(G) ⇒ H2(Γ) for every overgroup `Γ ≥ G` and every finite-index subgroup `Γ ≤ G`. In
   particular, among groups of supremum `0`, H2 is invariant under commensurability.

*Proof.*
1. Given `ε`, take a nontrivial pair over `G` with `min(a, b) < s(G) + ε`. By (F2) it is a nontrivial pair over `Γ`,
   so `r(Γ) < s(Γ) + ε`. By (F6), `r(Γ) ≥ s(Γ)`, so `r(Γ) = s(Γ)`.
2. By (F3), `(ka, kb)` is a nontrivial pair over `H`, and `min(ka, kb) < k s(G) + kε = s(H) + kε`. Conclude by (F6).
3. By Lemma 1.1, an overgroup has `s(Γ) ≤ 0`, so `s(Γ) = 0` and item 1 applies. By Lemma 1.2, a finite-index
   subgroup has `s(Γ) ≤ k·0 = 0`, and item 2 applies. If `G_1, G_2` are commensurable with supremum `0`, pass from
   `G_1` to the common finite-index subgroup by item 2, then up to `G_2` by item 1. ∎

**Proposition 3.3 (anatomy of a counterexample).** Let `s(Γ) < ∞` and `r(Γ) > s(Γ)` (H2 fails at `Γ`, possibly with
`r(Γ) = ∞`).
1. Every subgroup `G ≤ Γ` has `r(G) ≥ r(Γ)`. If H2(G) holds, then `s(G) = r(G) ≥ r(Γ) > s(Γ)`.
2. Every index-`k` subgroup `H ≤ Γ` has `r(Γ) ≤ r(H) ≤ k r(Γ)`.
3. Every overgroup `Γ' ≥ Γ` has `s(Γ') ≤ s(Γ)` and `r(Γ') ≤ r(Γ)`.
4. H2 fails at every subgroup `G ≤ Γ` with `s(G) = s(Γ)`, and at every overgroup `Γ'` of which `Γ` is an
   index-`k` subgroup with `s(Γ) = k s(Γ')`.

*Proof.* Items 1 and 3 (for `r`): (F2) pushes every nontrivial pair up. Item 3 (for `s`): Lemma 1.1. Item 2: the
lower bound is item 1; the upper bound is (F3) applied to pairs over `Γ` with `min(a, b)` near `r(Γ)`. Item 4 is
the contrapositive of Theorem 3.2(1) and (2). ∎

So a minimal counterexample (one of minimal supremum in its commensurability class, say) propagates: its gap
`r − s` cannot be repaired by any subgroup of the same supremum, and subgroups that do satisfy H2 sit at supremum
`≥ r(Γ)`.

## 4. What the obstruction leaves

**Remark 4.1 (the co-induction ledger).** Corollary D of
`coinduced-finite-subgroup-shifts-add-entropy-to-bernoulli` gives `Coind_F^G(Y) × K^G ≅ M^G` with
`H(M) = H(K) + H(Y)/|F|`. Assign to `Coind_F^G(Y) × K^G` the ledger value `H(K) + H(Y)/|F|`. Both sides then carry the
same value. Chains of such isomorphisms and products therefore relate `X_a` to `X_b` only through actions of equal
ledger, which gives `a = b`. This is a remark, not part of Theorem 2.3: the ledger is not claimed to be an
isomorphism invariant, only to be conserved by the recorded constructions.

**4.2 Survivors.** A derivation of H2 must use at least one step outside `T`, and that step must lower the excess.
The candidates are:
- **Cancellation.** `X_(a+t) ≅ X_(b+t) ⇒ X_a ≅ X_b` is the inverse of (T-prod) and lowers the excess by `t`. It is
  recorded dead on the target (`## Attempts`, "Cancellation from a high collapse"): no cancellation theorem for
  Bernoulli factors is known above `s`.
- **Primitive near-threshold isomorphisms.** These are seeds of excess `< ε` over some group `G`, carried to `Γ` along
  paths of defect `< ε` (Corollary 3.1). At `G` they are H2 up to `ε`.
- **Exact limits of approximate isomorphisms.** These are refuted on nonamenable groups
  (`spectral-gap-refutes-exactification-on-nonamenable-groups`).

So the transfer class (products, chaining, co-induction, finite-index restriction and Seward's equal-entropy
theorem, over any family of groups) dies at one invariant: the excess `min(a, b) − s(·)`. The death step is the
first (and each) transfer applied to a seed: the excess can only grow by the step's defect, and the target needs it
to tend to `0`.

Nothing here constructs a group with `0 < s < ∞` or `s = 0`, or proves any level rigid.
