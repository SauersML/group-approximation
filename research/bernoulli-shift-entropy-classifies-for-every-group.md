---
rg: 2
id: bernoulli-shift-entropy-classifies-for-every-group
kind: claim
title: Bernoulli shifts with different base entropy are non-isomorphic over every countably infinite group
root: true
refuted_by:
  - some-group-has-isomorphic-bernoulli-shifts-of-different-entropy
distinct_from:
  coset-bernoulli-action-is-essentially-free: that is freeness of one generalized Bernoulli action over a coset space; this is the isomorphism classification of ordinary Bernoulli shifts by base entropy, over all groups.
---

**OPEN.** Let `G` be a countably infinite group, and let `(L,λ)` and `(K,κ)`
be standard probability spaces with `H(L,λ) ≠ H(K,κ)`. Then the Bernoulli
shifts `G ↷ (L^G,λ^G)` and `G ↷ (K^G,κ^G)` are not isomorphic.

**Source.** B. Seward, *Bernoulli shifts with bases of equal entropy are
isomorphic*, arXiv:1805.08279 (J. Mod. Dyn. 2022). From the introduction, read
from the arXiv HTML on 2026-09-12:
- "As entropy is an isomorphism invariant, it follows that G↷(L^G,λ^G) and
  G↷(K^G,κ^G) are non-isomorphic whenever G is sofic (so the sofic entropy is
  defined) and H(L,λ)≠H(K,κ)."
- "If non-sofic countable groups G exist, then it is still unknown whether
  (2^G,u_2^G) and (3^G,u_3^G) are isomorphic."

The same paper proves that equal base entropy gives isomorphic Bernoulli shifts
over every countably infinite group, so this claim is exactly the missing half
of the classification. It holds for sofic groups, so a counterexample must be
nonsofic. Nonsofic groups now exist (`openai-leavitt-unit-nonsofic`).

**Relation to `every-group-has-positive-rokhlin-entropy-action`.** The route
`bernoulli-classification-via-positive-rokhlin-entropy` derives this claim from
that hypothesis and `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`:
- INF(G) follows for each group through products `P × G`, by Seward Theorem 1.11;
- INF(G) then gives Bernoulli Rokhlin entropy equal to base entropy;
- Rokhlin entropy is an isomorphism invariant.

Per group, the scope is narrower:
- INF(G) alone gives this claim for `G`;
- for one pair of finite base entropies `h_1 < h_2`, the weaker bound
  `h^Rok_sup(G) > h_1` suffices.

Necessary conditions on a counterexample group are recorded in
`bernoulli-entropy-counterexample-constraints`.

## Attempts

- **Origin and wiring.** The strategy lane `opportunity-mapper` opened this
  claim (item 2 of `research/artifacts/opportunity-map-2026-09-12.md`). Lane
  `bernoulli-entropy-classification` read the per-group statements of Seward
  II, wrote the route above and the counterexample constraints, and was merged
  into lane `rokhlin-entropy` on 2026-09-12.
- **No lower bound.** Every lower bound for Rokhlin entropy used here comes
  from sofic entropy or amenability. The attempts toward one without sofic
  models are recorded on `every-group-has-positive-rokhlin-entropy-action`.
- Weak isomorphism gives no obstruction. Every nonsofic group known here
  contains a nonabelian free subgroup, and over such groups every pair of
  nontrivial Bernoulli shifts is weakly isomorphic (Bowen, arXiv:0812.2718). A
  counterexample needs an actual isomorphism that changes base entropy.
- **Structure of failure and the approximate form (2026-09-12, lane
  ex-bernoulli-positive).**
  - All failures over one group form an additive subgroup `D(G)` of base-entropy
    differences with upward-closed witness sets. Classification over `G` is
    `D(G) = {0}`, failure is absorption `X_h ≅ X_h × X_d`, and collapse onto `X_∞`
    is total (`bernoulli-isomorphism-collapse-set-is-a-subgroup`).
  - The approximate form AINV(G), that `λ^G` is not a weak* limit of shift models of
    `K^G` when `H(λ) < H(κ)`, is equivalent to INF(G) and implies this claim for `G`
    (`rokhlin-entropy-is-the-bernoulli-approximation-threshold`). Over a group with
    finite supremum `s`, Bernoulli shifts above `s` approximate each other's measures
    by isomorphic models in both directions. There this claim says exactly that the
    approximations never close.
  - Every semicontinuous isomorphism invariant is constant above `s`
    (`semicontinuous-invariants-blind-above-rokhlin-supremum`). So a positive proof is
    a proof of INF(G) or uses an invariant that is not semicontinuous in the shift
    measure.
- **Seward's equal-entropy isomorphisms cannot collapse.** The isomorphism of
  arXiv:1805.08279, Theorem 3.2, fixes a common factor and recodes the remaining
  i.i.d. labels along each orbit of an aperiodic `T` in the pseudogroup by an
  isomorphism `ζ: (A^Z, α^Z) → (B^Z, β^Z)` from Ornstein's theorem for `Z`. Section 5:
  "it is necessary that (L^G,λ^G) and (K^G,κ^G) admit a non-trivial common factor and
  that they each have strong independence properties over this common factor". Such
  a `ζ` exists only when `H(α) = H(β)`. The proof's formula for `H(A, α)` equates it
  with `H(B, β)` exactly when `H(L) = H(K)`. So the construction preserves base
  entropy.
- **Amenable skew products are base-blind (argument, not landed as a claim).** Let `G`
  be finitely generated and nonamenable, and `m` symmetric, finitely supported and
  generating, with spectral radius `ρ < 1` (Kesten). The random-walk skew product
  `T(ω, x) = (σω, ω_0^(-1)·x)` on `(S^Z × L^G, m^Z × λ^G)` is a `Z`-action whose
  Kolmogorov–Sinai entropy is an isomorphism invariant of `G ↷ L^G`.
  - Read `ω_0` and `x` on the ball `B_r`. The entropy rate is
    `H(m) + H(λ)·lim_n E|∪_(k<n) w_k B_r|/n`, where `w_k` is the walk.
  - `P(|w_t| ≤ 2r) ≤ |B_(2r)| ρ^t`. Take the times `jt` with
    `|B_(2r)| ρ^t/(1 − ρ^t) ≤ 1/2`, so `t = O(r)`. Inclusion–exclusion over their
    balls gives `E|∪_(k<n) w_k B_r| ≥ n|B_r|/(2t)`.
  - So the rate is at least `H(m) + H(λ)|B_r|/O(r)`. This is unbounded in `r`,
    because nonamenable groups have exponential growth.
  - So the entropy is `∞` for every nontrivial base. Entropy of amenable functorial
    constructions sees only whether the base is trivial.
- **Coset Bernoulli actions separate bases trivially.** Suppose `H ≤ G` has only
  finitely many finite orbits on `G/H`, with union `F`. The `H`-invariant σ-algebra
  of `A^(G/H)` is then `(A^F)^H`, because `H` acts mixingly on the coordinates in
  infinite orbits (Neumann's lemma). It is atomic, with a number of atoms that
  increases with `|A|`. So rigidity or superrigidity theorems about non-free coset
  Bernoulli actions distinguish bases for a reason that is absent for free shifts,
  and they give nothing here.
- **Gaussian and Poisson structure.** The Gaussian action of `λ_R` and the Poisson
  suspension of `G ↷ G × [0,1]` are Bernoulli shifts with infinite base entropy. An
  isomorphism of actions need not respect a Gaussian or Poisson presentation, and the
  functorial input, the Koopman representation, is `λ^⊕N` for every nontrivial base.
- **Algebraic absorption and co-induced Ornstein (2026-09-12, lane ex-bernoulli-negative).**
  - Stable finiteness failure of `F_p[G]` is exactly algebraic self-absorption
    `(F_p^n)^G ≅ (F_p^n)^G × X_P` of a Bernoulli shift
    (`stable-finiteness-failure-is-algebraic-bernoulli-absorption`). A collapse is the same kind of
    absorption, with a Bernoulli factor in place of `X_P`.
  - The Leavitt relation `L ≅ L ⊕ L` gives a free ergodic self-square `X_L ≅ X_L²` over the unit group.
    No Leavitt-module dual action is a Bernoulli factor
    (`leavitt-module-dual-actions-are-self-squares-off-bernoulli`).
  - Seward's construction extends to shifts co-induced from finite subgroups, which add `H(Y)/|F|` to a
    Bernoulli shift (`coinduced-finite-subgroup-shifts-add-entropy-to-bernoulli`). On induced modules this
    is `log p` times the lifted p-adic trace, and module isomorphisms conserve that trace
    (`finite-subgroup-induced-absorption-conserves-entropy`). So algebra plus co-induced Ornstein never
    collapses.
  - The negation is `some-group-has-isomorphic-bernoulli-shifts-of-different-entropy`. The live
    constructive target is exact collapse above the Rokhlin supremum
    (`bernoulli-shifts-above-rokhlin-supremum-are-isomorphic`).
