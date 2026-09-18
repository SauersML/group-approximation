# gq-referee-b: `kazhdan-almost-v-central-v-elements-proof` and `normal-germ-extensions-of-v-have-only-finite-kazhdan-subgroups` (citation and scope lens)

Nodes as on origin/main at review time (lane bh-kazhdan-inputs). Referee a passed both (bdc9e959c).

Sources:
- BBGGHMS, *Centralizers in R. Thompson's group `V_n`*, arXiv:1107.0672, TeX at
  `gq/src/bh-kazhdan-inputs/CIV-1107.0672.tex`, 2631 lines;
- Belk–Hyde–Matucci (BHM), arXiv:2407.03149v1, TeX at `gq/src/bhm/`;
- the arXiv abstracts of Kaluba–Nowak–Ozawa and Kaluba–Kielak–Nowak.

**Verdict: PASS for both.**
- Every BBGGHMS input is at the lines cited, up to ±4.
- The combinatorial attracting set equals the topological one: this follows from BBGGHMS's decomposition
  `Per(α) = R_α ⊔ A_α ⊔ P_α`.
- (T) for `Aut(F_n)`, `n ≥ 5`, is pinned.
- BHM Corollary 2.10 is the right number.
- One scope wording point: the node's (a)/(b) regime is a variant of BHM's condition (3), not a restriction of it
  (W1).

## 1. `kazhdan-almost-v-central-v-elements-proof`: the BBGGHMS inputs

- **Revealing pairs exist.** Revealing pairs are defined at l.905–907: "If every component of `A−B` contains a
  repeller, and every component of `B−A` contains an attractor, then we say that `(A,B,σ)` is a revealing pair". Then
  l.909–910: "The discussion beginning section 10.7 in \cite{brinHigherV} proves that every element of `V_n` admits a
  revealing pair." ✓ This is a secondary pin of Brin, as the node says.
- **`torsionRevPair`**, l.1116–1133: "There is an integer `n` so that `α` has order `n` if and only if there is a tree
  pair `(A,B,σ)` representing `α` with `A = B`." ✓
  - So a revealing pair of an infinite-order element has `A ≠ B`.
  - With equal leaf counts, `B − A ≠ ∅`, and it contains an attractor by definition. ✓
- **`AttractorProps`**, l.1053–1075. Item 1: the attractor's name `γ_i Γ^∞` "represents a unique attracting fixed
  point `p_(γ_i)` in the interval `X_i` ... under the action of `⟨α^r⟩`". Item 3: "`⟨α⟩ ≅ Z`". ✓
  - The basin, l.~1085: "all points in `X_i` eventually limit to `p_(γ_i)` under repeated iteration of `α^(−r)`". Here
    `X_i` is the cone under `γ_i`. This is the node's "basin contains a cone". ✓
- **Finiteness of `𝒜_α`**, l.1100–1102: "We denote by `𝒜_α` the set of periodic attracting points of `α`, noting that it
  is a finite set." ✓ The node cites l.1098–1101; the exact line is 1102.

**The combinatorial attracting set equals the topological one** (the lane asked about this).
- l.1136–1139: "We further denote by `Per(α)` the set of all periodic points of `α`, that is
  `Per(α) = R_α ⊔ A_α ⊔ P_α`."
- `P_α` is "the points of `CS_n` which underlie the periodic neutral leaves" (l.1134–1135). A periodic neutral leaf is
  a cone mapped to itself by a power, by prefix replacement with the same prefix. So it is fixed pointwise, and its
  points are not topologically attracting.
- The points of `R_α` are repelling. `RepellerProps`, l.~1040–1045: points near them "eventually flow out ... never to
  return", so they are not attracting.
- The points of `A_α` are topologically attracting, with a cone basin, by `AttractorProps`.
- So the topologically attracting periodic points are exactly `A_α`, as the node claims. ✓

The remaining steps of the proof are the proof-gap lens's domain, and referee a passed them:
- the local form `u' = ue`;
- the fundamental domain;
- the descent to `V`, then Haagerup;
- the translation numbers.

The one citation among them, `thompson-v-has-haagerup-property`, is a landed node.

## 2. `normal-germ-extensions-of-v-have-only-finite-kazhdan-subgroups`

**The BHM definitions and the number.** Read in the BHM TeX:
- "finite germ extension" (l.154–160), `sing(G)` (l.162–165), and the group of germs `(G)_p = Stab_G(p)/RStab_G(p)`
  (l.185–187). The node uses these as defined. ✓
- **The number 2.10 is right.** §2 has a single theorem counter (l.39–58), and its environments are, in order:
  - Theorem 2.1 `thm:SingFixFiniteness`;
  - Notation 2.2;
  - Lemma 2.3;
  - Remark 2.4;
  - Propositions 2.5–2.9;
  - Corollary 2.10 `cor:MainFinitenessCorollary`, l.538.

**Corollary 2.10 (3)**, l.545–546: "Either `|(G)_p : (B)_p| < ∞` for each `p ∈ sing(G)`, or `(B)_p ⊴ (G)_p` for each
`p ∈ sing(G)` and `(G)_p/(B)_p` has type `F_n`." The node's hypothesis differs from this in three ways.
1. BHM's condition is a global either/or. The node allows a pointwise mixture of (a) and (b), which is weaker.
2. The node drops "`(G)_p/(B)_p` has type `F_n`", which is weaker again.
3. The node restricts (b) to eventually periodic points, which is stronger, as its Scope says.

So "These are the two alternatives of the germ hypothesis of Corollary 2.10 there, with (b) restricted to periodic
points" is inexact in directions 1 and 2. Those directions only enlarge the node's regime, so the theorem is not
affected.

What is affected is the phrase "the Corollary 2.10 regime", and with it the Consequence "must ... leave the Corollary
2.10 regime". The node's regime is not contained in BHM's. A host satisfying BHM's second alternative at an aperiodic
point lies outside the node's theorem, and the Scope correctly records this.

The consequence the node draws is sound as it states it: an input must leave the node's regime (a)/(b). It should not
be phrased as leaving BHM's regime (W1).

**Property (T), cited as not re-read.** Pinned from the arXiv abstracts:
- Kaluba–Nowak–Ozawa, arXiv:1712.07167 (Math. Ann. 375 (2019)): "a constructive, computer-assisted proof that
  `Aut(F_5)` ... has Kazhdan's property (T)". ✓
- Kaluba–Kielak–Nowak, arXiv:1812.03456 (Ann. of Math. 193 (2021)): "We prove that `Aut(F_n)` has Kazhdan's property
  (T) for every `n ≥ 6`. Together with a previous result of Kaluba, Nowak, and Ozawa, this gives the same statement for
  `n ≥ 5`." ✓
- `Out(F_n)` then has (T) as a quotient of `Aut(F_n)`. (T) passes to quotients, a standard fact (Bekka–de la
  Harpe–Valette, not read here). The node should say "as a quotient".

**The named hosts.** The node's Consequences cite Corollary 2 of
`normal-germ-extensions-of-thompson-v-contain-no-sl3z` for `VA` and for bounded-automata `V_2(G)`. BHM l.172 supports
the latter's germ-extension status: "if `G ≤ Aut(T_d)` is a bounded automata group, then the Röver–Nekrashevych group
`V_d G` is a finite germ extension of `V_d`". ✓

## Warnings

- **W1.** `normal-germ-extensions-...`: replace "These are the two alternatives of the germ hypothesis of Corollary
  2.10 there, with (b) restricted to periodic points". Suggested: "a pointwise variant of BHM Cor. 2.10(3), with no
  finiteness requirement on `(G)_p/(V)_p`, and with the normal alternative only at eventually periodic points". In
  the title and Consequences, say "this regime" rather than "the Corollary 2.10 regime".
- **W2.** `Out(F_n)`: add "(as a quotient of `Aut(F_n)`)". The KKN abstract states (T) only for `Aut(F_n)`.
- **W3.** `kazhdan-almost-v-...`: finiteness of `𝒜_w` is at l.1100–1102. Cite the `Per(α)` decomposition (l.1136–1139)
  for the equality of the combinatorial and topological attracting sets.
