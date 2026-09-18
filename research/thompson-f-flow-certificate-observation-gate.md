---
rg: 2
id: thompson-f-flow-certificate-observation-gate
kind: claim
title: An expansion flow for Thompson's F that reads only an observation Psi exists iff Psi has positive shadow defect, and profile plus tree count plus total caret count has defect zero, so all such flows die
distinct_from:
  thompson-f-finite-state-flows-cannot-prove-nonamenability: that kills rules reading a finite automaton profile and the tree count by one averaging model; this proves the averaging condition is also necessary (a minimax equivalence for every observation), and extends the kill to rules that also read the total caret count, a gap that claim lists.
  thompson-f-nonamenable-iff-some-monomial-set-doubles: that makes non-amenability equivalent to doubling of a monomial set; this restates doubling as positive shadow defect of the identity observation and classifies which coarser observations can never witness it.
  thompson-f-moment-data-cannot-certify-nonamenability: that kills finitely many return probabilities by a spectral measure reaching +-1; this kills local transport rules by a dual probability law, a different certificate shape.
  thompson-f-end-rigid-schreier-graphs-are-amenable: that proves amenability of certain Schreier graphs; this shows every Schreier graph with Følner sets gives defect zero, which is the flow form of that kill, and adds observations that are not Schreier graphs.
  thompson-f-ore-obstructions-must-see-finite-support: that rules out leading-term invariants for non-Ore pairs in the group ring; this is about transport flows on the monoid, not about ring equations.
  thompson-f-evacuation-schemes-need-capacity-three: that bounds capacities of evacuation schemes on one Cayley graph; this is capacity-free and says which information a flow must read.
---

**ESTABLISHED** through `thompson-f-flow-certificate-observation-gate-proof` (direct proof; one
classical import, Sion's minimax theorem, quoted in its standard form; not independently reviewed; no
priority claimed).

**Setting.** `M` is the positive monoid of `F`, identified with forests as in
`thompson-f-finite-state-flows-cannot-prove-nonamenability`. For finite `S ⊆ M` and any map `Ψ : M → X`,
a *rule reading `Ψ`* is `w(s, y) = G(s, Ψ(y))` with `G >= 0`. It has out-sum `Σ_s G(s, Ψ(y))` at `y` and
in-sum `Σ_(s y = z) G(s, Ψ(y))` at `z`. For probability vectors `μ, η` on `M` put `ρ^η_s(y) = η(s y)` and

`D_λ(μ, η) = Σ_(s ∈ S) || (Ψ_* μ − λ Ψ_* ρ^η_s)_+ ||`,   `δ_λ(Ψ) = inf_(μ, η) D_λ(μ, η)`.

**Theorem A (the gate is exact).** For `λ >= 1`, there is a rule reading `Ψ` with bounded in-sum and
`inf out > λ · sup in` iff `δ_λ(Ψ) > 0`. The payoff `E_μ out − λ E_η in` is bilinear in `G ∈ [0,1]^(S × X)`
and `(μ, η)`, its maximum over `G` is `D_λ(μ, η)`, and Sion's theorem exchanges `max` and `inf`.

Consequences.
- *(A.1, class kill.)* If `δ_1(Ψ) = 0`, no rule reading `Ψ` is a certificate with ratio `> 1`.
- *(A.2.)* The averaging principle (Lemma 3.1 of the finite-state proof) is the special case `μ = η`.
- *(A.3, the gate.)* `F` is not amenable iff `δ_λ(id_M) > 0` for some `λ > 1` and some
  `S = S_(m+1,m+d+1)`. So every flow-type proof of non-amenability is a proof that some observation has
  positive shadow defect, and every flow-type kill is a shadow law.
- *(A.4.)* Coarsening an observation does not increase `δ`, so dead observations form a down-set.

**Dead observations** (`δ_1 = 0`).
- *B.1.* Constant `Ψ`: a point mass on a common right multiple of `S`, which exists by the Ore property.
  Calibration: the free monoid on `{a, b}` has `w ≡ 1` with ratio 2.
- *B.2 (group version).* `Ψ(g) = gH` whenever `F` acting on `F/H` has Følner sets. This covers every
  end-rigid and every co-amenable `H`.
- *B.3.* A finite automaton profile and the tree count (Theorem 4.3 of the finite-state proof).
- *Theorem B (new).* A finite automaton profile, the tree count and the total caret count `|y|`, hence
  also the leaf count. The shadow law pads each random forest with a right comb whose length is uniform
  over a long progression of its pumping period. It uses the product invariant `Q × Z/p`, which carries
  an idempotent measure, so a split changes the caret count only by a bounded multiple of `p` and the two
  laws differ by `O(1/L')`.

**Where each stalled flow attempt dies.**

| attempt | observation read | dies at |
|---|---|---|
| constant or degree-only transport | constant, `N`, `|y|` | B.1, Theorem B |
| Schreier graphs of natural `F`-sets | `gH` | B.2 |
| finite-state expansion flows | profile, `N` | B.3 |
| same plus total caret or leaf count | profile, `N`, `|y|` | Theorem B |
| any coarsening of these | `φ ∘ Ψ` | A.4 |

The invariant they share is a *dominated shadow law*: probability laws `μ, η` whose pushforwards under
`Ψ` satisfy `Ψ_* μ <= λ Ψ_* ρ^η_s` up to `ε`, for every `s`. By Theorem A that is the only way a
flow class can die, and its absence for `id_M` is non-amenability.

**Scope.**
- Not covered: observations reading unbounded data of individual trees (sizes, depths, shapes), which
  carry no idempotent measure; and finite-state readings of both forests of a reduced diagram (flows on the
  Cayley graph of `F`), where reduction cancels carets and no shadow law is built here.
- Not an obstruction: finite windows. `F` is finitely presented and every nontrivial normal subgroup
  contains `[F,F]`, so a large enough labelled ball determines `F` among marked groups. Window-reading
  rules cannot be killed by indistinguishability, only by a shadow law.
- Moment data (`thompson-f-moment-data-cannot-certify-nonamenability`) and leading terms
  (`thompson-f-ore-obstructions-must-see-finite-support`) die by analogous dual objects, but they are not
  flows and are not instances of Theorem A.
- The theorem proves neither answer. It kills a class of witnesses for `thompson-f-is-not-amenable`.
