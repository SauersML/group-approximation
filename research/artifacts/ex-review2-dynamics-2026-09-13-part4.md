# EX review 2, dynamics: part 4. Bernoulli bridge nodes

Lane `ex-verify2-dynamics`, tip `6dd68ce8d`.
- **Lanes.** ex-bernoulli-rokhlin-complete (a091c1f300, 71a738c65d, 28228d886b), ex-bernoulli-zero-supremum
  (b38ee6bf9a, cdabc1905f) and ex-bernoulli-positive (9c34e9e7f5).
- **First pass.** Dynamics part 2, §13.
- **Here.** The only established claim in this cluster is re-derived. The open bridges and the routes are checked
  for statement fidelity and firing.

| node | status at `6dd68ce8d` | verdict |
|---|---|---|
| `generators-dense-iff-zero-rokhlin-entropy` (+ `-proof`) | established | PASS (second pass) |
| `iid-generators-dense-at-zero-rokhlin-supremum` | OPEN | labelled correctly; Attempts checked |
| route `zero-supremum-collapse-via-dense-iid-generators` | unfired | PASS as an implication |
| `zero-rokhlin-supremum-forces-bernoulli-collapse` | OPEN | labelled correctly |
| `bernoulli-shifts-above-rokhlin-supremum-are-isomorphic` | OPEN | labelled correctly; the "null factor" Attempt checked |
| route `positive-rokhlin-via-classification-and-collapse` | unfired | the implication is correct |
| route `leavitt-zero-supremum-and-collapse-give-bernoulli-failure` | unfired | the implication is correct |

## 4.1 `generators-dense-iff-zero-rokhlin-entropy`: PASS

**Item 1, `⇒`.** For a generating `α`, `d^Rok(α, {X}) = H(α | {X}) + H({X} | α) = H(α) >= h^Rok_G(X)`. So density
near `{X}` forces `h^Rok_G(X) = 0`.

**Item 1, `⇐`.**
- *Step 1.* `μ(R)H_(μ_R)(β) = Σ μ(B_i ∩ R) log(μ(R)/μ(B_i ∩ R)) <= Σ φ(μ(B_i ∩ R))`, since `log μ(R) <= 0`.
  - The tail `i > N` is at most `Σ_(i>N) φ(μ(B_i)) < ε/8`, by monotonicity of `φ` on `[0, 1/e]`.
  - The head is at most `Nφ(r)`, because `μ(B_i ∩ R) <= r <= 1/e`.
- *Step 2.* Seward's Theorem 2.3 (arXiv:1405.3604; PASS verbatim in dynamics part 2, §13) with trivial factor
  gives a pre-partition `γ = {A_0, A_1}` of total mass `r`, whose reduced σ-algebra is everything. The hypothesis
  is `h^Rok_G(X) = 0 < r·log 2`.
  - Then `α = {B_i ∖ R} ∪ {A_0, A_1}` restricts to `γ` on `R`.
  - By Lemma 2.2 of the same paper, `α` generates.
- *Step 3.*
  - `α <= β ∨ ρ` with `ρ = {X ∖ R, A_0, A_1}`, so `H(α|β) <= H(ρ) = φ(1−r) + 2φ(r/2) = h_2(r) + r log 2`.
  - Off `R` the atom of `α` determines the atom of `β`. So `H(β|α) = Σ_(j=0,1) μ(A_j)H_(μ_(A_j))(β) < ε/2`, by
    Step 1 with `μ(A_j) = r/2 <= r_0`.
  - Hence `d^Rok(α, β) < 3ε/4`.

**Item 2.**
- Seward II Theorem 1.10 (`seward-per-group-rokhlin-entropy-of-bernoulli-shifts`) gives
  `h^Rok(K^G) = min(H(κ), h^Rok_sup(G))`.
  - Density in one Bernoulli shift with finite nontrivial base forces `min(H(κ), s) = 0`, so `s = 0`.
  - If `s = 0`, every free ergodic action has Rokhlin entropy `0`, and item 1 applies.
- The infinite-entropy case is handled through the dichotomy import (S6). That import was PASSed in dynamics part 2,
  §13d. It is not re-derived here.

**Item 3.** The perturbation lives on `R`, with `μ(R) = r`, which can be taken `<= ε`. Window patterns change only
on `∪_(w∈W) wR`, of measure `<= |W|r`.

**Credit.** The node says item 1 `⇐` is a direct consequence of Seward's small-support generators. That attribution
is accurate, and the novelty claim is bounded to §§1–2 of arXiv:1405.3604, as the node says.

## 4.2 Open bridges: statement fidelity and firing

- **`iid-generators-dense-at-zero-rokhlin-supremum`: OPEN.**
  - *"Predictable recodings capture nothing."* Condition on `ζ` and on `ξ` at the sites earlier in the
    `ζ`-measurable order. Then `ξ(g)` still has law `λ`, because `ξ` is i.i.d. and independent of `ζ`. A
    `λ`-preserving permutation keeps that law, so the law of `ξ'` on any finite window is `λ^F`, independent of
    `ζ`.
  - This is correct. The node draws only the stated consequence: such recodings add no information about `ζ`.
- **`zero-supremum-collapse-via-dense-iid-generators`.**
  - `Ind_λ(X)` is closed in the complete space of `L`-labelled partitions: joint laws of finitely many translates
    are Lipschitz in `μ(ξ != ζ)`.
  - `U_(Q,m)` is open, since `H(Q | ξ^W)` depends continuously on the joint law.
  - The Baire step is valid but redundant: density plus non-emptiness already gives one generating i.i.d.
    partition, hence `6^G ≅ 2^G`. The first pass noted the same. The route stays unfired, because its premise is open.
- **`zero-rokhlin-supremum-forces-bernoulli-collapse`: OPEN.**
  - It is labelled OPEN, and its Payoff items are stated as implications.
  - The sentence "a positive proof of the root would then prove Gottschalk's surjunctivity conjecture and Kaplansky's
    direct finiteness conjecture" recalls Seward's remark that positive Rokhlin entropy for every group has these
    consequences. It was not re-read against arXiv:1405.3604 here.
- **`bernoulli-shifts-above-rokhlin-supremum-are-isomorphic`: OPEN.**
  - *Reformulation.* `L^G ≅ K^G` iff `K^G` has a generating partition with law `λ` and independent translates.
  - *The null-factor Attempt.* If `K^G = F ∨ σ-alg_G(ζ)`, with `ζ` Bernoulli over `F` and `H(ζ) = b > 0`, then
    `(K^G, F)` is a product of two Bernoulli shifts. Seward's Proposition 6.5 (arXiv:1501.03367) then gives
    relative Rokhlin entropy `min(b, s) > 0`, so `F` is not null. This is correct as written.

**Firing.** No route of these lanes fires into `every-group-has-positive-rokhlin-entropy-action`,
`some-group-has-isomorphic-bernoulli-shifts-of-different-entropy` or
`bernoulli-shift-entropy-classifies-for-every-group`. All three are OPEN at `6dd68ce8d`.
