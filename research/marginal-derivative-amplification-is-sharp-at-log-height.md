---
rg: 2
id: marginal-derivative-amplification-is-sharp-at-log-height
kind: claim
title: "Moore's marginal-derivative amplification gives exactly logarithmic height; its tower bound is optimal for the method"
distinct_from:
  thompson-f-folner-function-exceeds-every-tower: that imports Moore's tower lower bound for F; this abstracts Moore's derivative step, re-proves it with an explicit rate, and shows that no argument of that shape can give more than logarithmic height, so the tower is the limit of the method.
  thompson-f-ramsey-amplification-needs-unbounded-tower-overhead: that concerns Ramsey-style amplification of finite colourings; this concerns the Følner-mass bookkeeping of a partial derivative map with a marginal bad set.
---

**ESTABLISHED** by `marginal-derivative-amplification-is-sharp-at-log-height-proof` (not yet refereed).

**Setting.**
- `G` is a group, `Γ ⊆ G` is finite and symmetric, and `G` acts partially on a set `S`, as in
  Moore, arXiv:0905.1118v7, Def. 3.1.
- For a finitely supported `μ : S → [0,∞)`, write
  `bd(μ) = Σ_{γ∈Γ} Σ_{s∈S} |μ(s·γ) − μ(s)|`. Following Moore, `μ(s·γ) = 0` when `s·γ` is
  undefined. `μ` is weighted `ε`-Følner iff `bd(μ) < ε μ(S)`.
- A **derivative datum** is a total map `∂ : S → S` together with a set `A ⊆ S` (the good set)
  satisfying condition **(E′)**: for `s ∈ A` and `γ ∈ Γ`, `s·γ` is defined iff `∂(s)·γ` is
  defined, and then `∂(s·γ) = ∂(s)·γ`.
- The bad set `B = S ∖ A` is **`c`-thin** if `μ(B) ≤ c·bd(μ)` for every finitely supported
  `μ ≥ 0`. Every set that is marginal in Moore's sense (Def. 3.3) is `c`-thin for some `c`, by his
  Lemma 3.10.
- The **height** is `h(s) = sup{ n : s, ∂s, …, ∂^{n−1}s ∈ A }`.

**Theorem A (amplification, explicit rate).** Suppose `B` is `c`-thin, and put `q = 1 + 2c|Γ|`.
1. For every finitely supported `μ ≥ 0` and every `n ≥ 0`,
   `μ({h ≥ n}) ≥ μ(S) − bd(μ)·(qⁿ − 1)/(2|Γ|)`.
2. Hence every weighted `ε`-Følner `μ` has a point `s` in its support with
   `h(s) ≥ ⌊log_q(1 + 2|Γ|/ε)⌋`.
3. Suppose also `|·| : S → ℕ_{≥1}` satisfies `|s| ≥ φ(|∂s|)` on `A`, for some nondecreasing `φ`,
   and put `m_* = min{|∂s| : s ∈ A}`. Then that point has `|s| ≥ φ^{(n)}(m_*)`, with
   `n = ⌊log_q(1 + 2|Γ|/ε)⌋`.

**Moore's instance.** Take `S = 𝒯`, the finite rooted binary trees, with the partial right action
of `F`, and `Γ = {x0^±1, x1^±1}`. Take Moore's `∂`, with good set
`A = {T : Γ acts properly on ∂T}`. This is a derivative datum:
- (E′) holds by his Lemma 5.5;
- `B` is marginal by his Lemma 5.12;
- `φ(m) = ⌊2^{m−2}⌋ + 1` by his Lemma 5.4, with `m_* ≥ 4`.

Theorem A then gives the tower of height `≍ log(1/ε)` in his Theorem 1.1.

**Theorem B (sharpness).** Fix an integer `K ≥ 2`. There is a derivative datum with the following
properties.
- It is a partial `F`-set with Moore's `Γ`: `F` acts through `F → ℤ`, `x0 ↦ 1`, `x1 ↦ 0`.
- (E′) holds, in the strong form where both sides are always defined on `A`.
- The bad set `B` is `K`-thin and is 1-marginal in Moore's formal sense (Def. 3.3).
- For every size labelling one likes, `|s| = φ(|∂s|)` holds on `A`.
- For every `j`, there is a set `P_j` that is `ε`-Følner for every `ε > 2/(3K^j)` and on which
  every point has height `≤ j`.

So in this datum the least achievable height is `≤ log_K(2/(3ε)) + 1`, against the guarantee
`log_{8K+1}(1 + 8/ε)` of Theorem A. The multiplicative loss per derivative step is realized: the
boundary-to-mass ratio of the pushed measure grows by the factor `K` at every level.

**Composition gives nothing.** `∂^r` with good set `{h ≥ r}` is again a derivative datum. Its bad
set is `c_r`-thin with `c_r = (qʳ − 1)/(2|Γ|)`, so `q_r = qʳ` and the rate is unchanged.

**Class killed.** Consider any Følner lower-bound argument whose inputs are a derivative datum on a
partial `G`-set, a marginal or merely thin bad set, and a size contraction `|s| ≥ φ(|∂s|)`.
- Such an argument cannot certify height more than `log_c(1/ε) + O(1)`. This holds even for
  `G = F` with Moore's generators.
- *Invariant:* the ratio `bd(μ_i)/μ_i(S)` of the successive pushed measures `μ_{i+1} = ∂_*(μ_i|_A)`.
- *Where every member dies:* the restriction step `μ ↦ μ|_A` (Moore's Lemmas 3.11–3.12, 5.13).
  Removing a mass `≤ c·bd` can multiply the boundary by `1 + 2c|Γ|`, and Theorem B shows that
  it does.
- **Consequence for `F`.** Reaching Moore's own open question (Question 1.2 of 0905.1118: is
  there a primitive recursive bound?) needs a better contraction `φ`, not more height. That
  prerequisite is isolated as `thompson-f-trees-carry-an-ackermann-derivative-hierarchy`.

**Scope.**
- Moore's lemmas are quoted verbatim from the TeX source of arXiv:0905.1118v7 in the route.
- Theorem A reproves his Lemmas 3.4 and 3.11 in the form needed.
- Theorem B is self-contained.
