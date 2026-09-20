# Bernoulli cost on the space of marked groups (2026-09-20)

Author: swarm-0917-w23-w23-fp-pull (transplanter, logic-computability).
This artifact backs `fpbs-bernoulli-cost-usc-on-marked-groups`.

## 0. Setting

- `G_k` is the space of `k`-marked groups `(Γ, S)`, `S = (s_1, …, s_k)`, with the
  topology in which `(Γ_n, S_n) → (Γ, S)` iff for every `R` the balls of radius `R`
  agree eventually. Equivalently, for each word `w` of length `≤ R` in the free group
  `F_k`, `w =_{Γ_n} 1` iff `w =_Γ 1`, for `n ≥ n(R)`.
- Finite marked groups are finitely presented with finitely many quotients, so they
  are isolated. The infinite ones form a closed subspace `G_k^∞`.
- For infinite `Γ`, `s_Γ` is the shift on `([0,1]^Γ, λ^Γ)`, with
  `(g·x)(h) = x(g^{-1}h)`. It is essentially free.
- `C*(Γ) := C(s_Γ)`. This is the maximum free-action cost:
  - `fpbs-bernoulli-maximal-cost` for finitely generated `Γ`;
  - `fpbs-finite-cost-transfers-up-weak-containment` with
    `abert-weiss-free-actions-weakly-contain-bernoulli` for countable `Γ`.

## 1. Theorem (upper semicontinuity)

`C* : G_k^∞ → [1, k]` is upper semicontinuous.

**Step 1 (a finite graphing with an exact repair).** Fix `ε > 0` and write `μ = λ^Γ`.
Choose a graphing of `E = E_{s_Γ}` with cost `< C*(Γ) + ε`. Split each piece along
the countably many group elements it realises, so that the graphing is
`Φ = (γ_j|A_j)_{j ≥ 1}` with `γ_j ∈ Γ`, Borel `A_j`, and `Σ_j μ(A_j) < C*(Γ) + ε`.

- For `J, L ∈ N`, let `Ψ_{J,L}` be `(γ_j|A_j)_{j ≤ J}`.
- Let `D_i^{J,L}` be the set of `x` such that `s_i x` is not reached from `x` by a
  `Ψ_{J,L}`-path of length `≤ L`.
- For a.e. `x`, some finite `Φ`-path joins `x` to `s_i x`. That path uses finitely
  many indices. So `D_i^{J,L}` decreases to a null set as `J, L → ∞`.
- Fix `J, L` with `Σ_i μ(D_i^{J,L}) < ε`.
- Then `Ψ_{J,L} ∪ {s_i|D_i^{J,L} : i ≤ k}` generates `E`. Every `x` is joined to
  `s_i x`, either within `L` steps of `Ψ` or by the added edge. `S` generates `Γ`,
  so every orbit is connected.
- Its cost is `< C*(Γ) + 2ε`.

**Step 2 (cylinder domains).** A *cylinder set* over a finite window `W ⊂ Γ` is a
finite Boolean combination of atoms `{x : x(w) ∈ I}`, where `w ∈ W` and `I` is a
rational interval.

- Cylinder sets are dense in the measure algebra. So choose cylinder sets `A'_j` with
  `μ(A_j Δ A'_j) < δ` for `j ≤ J`, and put `Ψ' = (γ_j|A'_j)_{j ≤ J}`.
- Let `D'_i` be the set of `x` such that `s_i x` is not reached from `x` by a
  `Ψ'`-path of length `≤ L`.
- Let `B` be the finite set of products of at most `L` letters `γ_j^{±1}` (`j ≤ J`).
- A `Ψ`-path of length `≤ L` from `x` visits only the points `βx`, `β ∈ B`.
- It checks only membership of such points in `A_j` or in `γ_j A_j`. The latter means
  membership of `γ_j^{-1} β x` in `A_j`.
- Unless `βx ∈ A_j Δ A'_j` for some `β ∈ B B'`, `j ≤ J`, the same path is a
  `Ψ'`-path. Here `B' = {1} ∪ {γ_j^{-1}}`.
- By invariance of `μ`, `μ(D'_i) ≤ μ(D_i^{J,L}) + |B B'| J δ`.
- Choose `δ` so that `Ψ' ∪ {s_i|D'_i}` has cost `< C*(Γ) + 3ε`. It generates `E`
  exactly, as in Step 1.

**Step 3 (everything is a finite-ball event).** Freeness gives the following. For
a.e. `x` and each path pattern `p = ((j_1, e_1), …, (j_m, e_m))`, `m ≤ L`, write
`β_p = γ_{j_m}^{e_m} ⋯ γ_{j_1}^{e_1}`. Then the endpoint `β_p x` equals `s_i x` iff
`β_p = s_i` in `Γ`. Hence, up to a null set,

```text
Γ-side:  X \ D'_i = ⋃ { Valid_p : |p| ≤ L, β_p =_Γ s_i },
```

where `Valid_p` is the intersection over `t ≤ m` of the domain conditions of step `t`.
Each domain condition is `β x ∈ A'_j` or `γ_j^{-1} β x ∈ A'_j`. Because
`(βx)(w) = x(β^{-1} w)`, every `A'_j`, `D'_i` and `s_i|D'_i`-domain is a Boolean
combination of atoms `{x(u) ∈ I}`. Here `u` runs over a finite set `U` of group
elements, each given by a fixed word of length `≤ R_0` in `S`.

**Step 4 (measures depend only on the equality pattern).**
- Under `λ^Γ` the coordinates at distinct group elements are i.i.d. uniform.
- Coordinates at equal group elements coincide.
- So the measure of a Boolean combination of atoms `{x(u) ∈ I}`, `u ∈ U`, is a
  function of the formula and of the partition of the word set `U` into classes of
  words that are equal in `Γ`.
- That partition, and the set of patterns `p` with `β_p =_Γ s_i`, are both determined
  by the ball of radius `R = 2R_0 + 2` of `(Γ, S)`.

**Step 5 (transfer).** Let `(Γ_n, S_n) → (Γ, S)` in `G_k^∞`, and take `n` with
`B_R(Γ_n) = B_R(Γ)`.

- Read every word defining `γ_j`, `W` and the atoms in `Γ_n`.
- Let `A_j^{(n)}` be the same Boolean formulas in `[0,1]^{Γ_n}`.
- Let `D_i^{(n)}` be the set where `s_i x` is not reached by a length-`≤ L` path of
  `Ψ^{(n)} = (γ_j^{(n)}|A_j^{(n)})_{j ≤ J}`.
- `s_{Γ_n}` is free because `Γ_n` is infinite. So Step 3 applies verbatim in `Γ_n`,
  and `D_i^{(n)}` is given by the same formula as `D'_i`: the pattern set agrees on
  the ball.
- By Step 4, `μ_n(A_j^{(n)}) = μ(A'_j)` and `μ_n(D_i^{(n)}) = μ(D'_i)`.
- As in Step 1, `Ψ^{(n)} ∪ {s_i|D_i^{(n)}}` generates `E_{s_{Γ_n}}`.
- Hence `C*(Γ_n) < C*(Γ) + 3ε` for all large `n`, and
  `limsup_n C*(Γ_n) ≤ C*(Γ)`. ∎

**Corollary 1.1.** In `G_k^∞`:
- `{C* < t}` is open for every `t`;
- `{Γ : s_Γ has cost 1}` is a `G_δ`;
- `C*` is Baire class 1, so its points of continuity form a dense `G_δ` of `G_k^∞`.

## 2. Theorem (C* is not lower semicontinuous)

Let `Γ_n = ⟨a, b | [a, b^n]⟩` for `n ≥ 2`, marked by `(a, b)`.

1. **Structure.** `Γ_n = ⟨a, c | [a,c]⟩ *_{c = b^n} ⟨b⟩ = Z^2 *_Z Z`.
2. **Convergence.** `Γ_n → F_2` in `G_2`.
   - Let `w` be a nonempty freely reduced word in `a, b` of length `< n`.
   - Every `b`-syllable of `w` is `b^k` with `0 < |k| < n`. It lies in `⟨b⟩ \ ⟨b^n⟩`.
   - Every `a`-syllable is `a^j` with `j ≠ 0`. It lies in `Z^2 \ ⟨c⟩`.
   - So `w` is a reduced alternating product in the amalgam, and `w ≠ 1` by the normal
     form theorem for amalgamated products (Serre, *Trees*, I.1.2, Thm 1; Lyndon–Schupp
     IV.2.6).
   - Hence `B_{⌊(n-1)/2⌋}(Γ_n) = B_{⌊(n-1)/2⌋}(F_2)`.
3. **`C*(Γ_n) = 1`.**
   - `N = ⟨b^n⟩` is central: `b^n` commutes with `a` by the relation, and with `b`.
   - `N` is infinite, because `a ↦ 0`, `b ↦ 1` maps `b^n` to `n ≠ 0` in `Z`.
   - So `N ◁ Γ_n` is infinite with centralizer `Γ_n`, and
     `fpbs-infinite-centralizer-forces-price-one` gives fixed price one.
4. **`C*(F_2) = 2`.**
   - `C*(F_2) ≤ 2` from the two generators.
   - `C*(F_2) ≥ 1 + β_1^(2)(F_2) = 2` by `fpbs-amen2-betti-cost-input`.
   - `β_1^(2)(F_2) = -χ(F_2) = 1`.

So `liminf C*(Γ_n) = 1 < 2 = C*(F_2)`, and `C*` is not lower semicontinuous at `F_2`.
The same happens for `β_1^(2)`. By `fpbs-amen2-betti-cost-input`,
`β_1^(2)(Γ_n) ≤ C*(Γ_n) - 1 = 0`, while `β_1^(2)(F_2) = 1`.

**Free groups of every rank.** For `k ≥ 2`, take
`Γ_n^{(k)} = ⟨a_1, …, a_k | [a_i, a_1^n], 2 ≤ i ≤ k⟩`. This is
`(Z × F_{k-1}) *_{c = a_1^n} ⟨a_1⟩`, with `c` the generator of the `Z` factor. The same
syllable argument applies: a nontrivial word in `a_2, …, a_k` lies in
`F_{k-1} \ ⟨c⟩`. So `Γ_n^{(k)} → F_k`. Here `a_1^n` is central and infinite, so
`C*(Γ_n^{(k)}) = 1`, while `C*(F_k) = k`.

**Corollary 2.1 (no ball-local lower certificates at free groups).** For every `R`,
the `R`-ball of `F_k` is the `R`-ball of a group of fixed price one. So no statement
of the form "`B_R(Γ) = B_R(F_k)` implies `C*(Γ) ≥ t`" holds with `t > 1`. The same is
true for "implies `β_1^(2)(Γ) ≥ t`" with `t > 0`.

## 3. Arithmetic form

**Corollary 3.1.** Let `Γ` have decidable word problem. Then `C*(Γ)` is a
right-computable real, uniformly in a decider.

- Enumerate all finite data `(J, words for γ_j, rational cylinder formulas for A'_j, L)`.
- Each datum yields, through Steps 3–5, an exactly generating graphing of `E_{s_Γ}`.
- Its cost is a finite sum of `λ`-measures of rational box conditions on finitely many
  coordinates, with coordinates identified according to the word problem. That sum is
  a rational number computable from the datum.
- Steps 1–2 show that the infimum of these costs is `C*(Γ)`.

With `decidable-groups-have-right-computable-l2-betti-numbers`, both sides of
`C*(Γ) = 1 + β_1^(2)(Γ)` are right-computable. The inequality `C* ≤ 1 + β_1^(2)` then
reads `∀q ∈ Q (β_1^(2) < q - 1 → C* < q)`, a `Π^0_2` sentence relative to the
decider. A counterexample,
`∃q (C* ≥ q ∧ β_1^(2) < q - 1)`, is `Σ^0_2` and has no finite witness: `{C* ≥ q}` is
only `Π^0_1`. This matches the "no finite certificate" finding recorded on
`fpbs-farber-chain-rank-gradient-exceeds-l2-betti`.

## 4. The class killed: marked-limit transfers

**Class M.** Approaches that prove `C*(Γ) = 1 + β_1^(2)(Γ)`, which is cycle-tail
compactness for `s_Γ`, at a target `Γ` in two steps:

1. prove it on marked groups `Γ_n → Γ`, for example finitely presented covers
   `F_k/⟨⟨r_1, …, r_n⟩⟩`, small-cancellation or hyperbolic approximants, or free
   markings of limit groups;
2. pass to the limit using ball-local or semicontinuity information on `C*` and
   `β_1^(2)`.

**Invariant.** Both `C*` (Theorem 1) and `β_1^(2)` (Pichot's upper semicontinuity)
satisfy only `limsup_n f(Γ_n) ≤ f(Γ)`.

**Where every member dies: step 2, at the upper bound for `C*(Γ)`.**
- From `C*(Γ_n) = 1 + β_1^(2)(Γ_n)`, the semicontinuities yield only lower bounds
  `C*(Γ) ≥ limsup_n C*(Γ_n) = 1 + limsup_n β_1^(2)(Γ_n)`.
- These are already implied by Gaboriau's inequality and Pichot.
- The missing inequality `C*(Γ) ≤ 1 + β_1^(2)(Γ)` needs an upper bound on `C*(Γ)` from
  the approximants, that is, lower semicontinuity of `C*` along the sequence.
- Theorem 2 shows that lower semicontinuity fails even at `F_k`, where the equality is
  known to hold.
- So the transfer is not a consequence of any ball-local information.
- Adding convergence `β_1^(2)(Γ_n) → β_1^(2)(Γ)` does not help. The transfer is then
  equivalent to continuity of `C*` along the sequence, which is the conclusion itself.

**What survives.**
- Arguments that bound `C*(Γ)` from above by a graphing built in `Γ` itself, which is
  the content of the node's other Attempts.
- Arguments that use a non-local input, such as the rank-gradient or sofic topology of
  Farber chains, where `C*` is not known to be semicontinuous at all.
