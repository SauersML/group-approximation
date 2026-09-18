# Referee report (citation/hypothesis lens): three nodes of lane gq-infinite-primes

Referee: lane gq-referee-b, 2026-09-17. Reviewed as landed at 4cd432d26:
- `z-localized-embeds-in-fp-kazhdan-steinberg-group`;
- `steinberg-rf-forces-ring-rf-proof`;
- `z-localized-embeds-in-fg-rf-soluble-group`, with the wording in `z-localized-embeds-in-fp-rf-group`.

## Verdicts

- **(1) `z-localized-embeds-in-fp-kazhdan-steinberg-group`: PASS**, with a rank note (R1).
- **(2) `steinberg-rf-forces-ring-rf-proof`: PASS.** The Milnor citation is correct in substance, but it can be
  dropped (R2).
- **(3) Wording against the sources: PASS**, with one attribution precision (R3).

## (1) Finite presentation and (T) for `St_N(R_l)`

`R_l = Z⟨u, x, x', B, e | xx' = x'x = 1, xu = (u+l)x, B(u+1) = (u+1)B = 1, ue = eu = 0, e^2 = e⟩`
has 5 generators and 8 relators. It is a finitely presented unital associative `Z`-algebra, in exactly the sense
of Krstić–McCool Theorem 3 as transcribed (Khanh arXiv:2609.08428v1, Thm 6.1): "a quotient of a free associative
unital ℤ-algebra on finitely many generators by a finitely generated two-sided ideal". **It matches.**

- **R1 (rank).** At `N = 4` the statement rests only on Krstić–McCool, via a secondary source; the primary is
  unread. For `N >= 5`, gq-referee-c's direct proof applies (passed in
  `gq-referee-b-steinberg-direct-finite-presentation.md`), with no literature input. If `N >= 5` suffices
  downstream, state the node for `N >= 5`, or note which rank needs the import.
- **(T).** Ershov–Jaikin-Zapirain, arXiv:0809.4095v2, Theorem 1.1: "Let R be a finitely generated (associative)
  ring with 1 and n≥3 …", with "we prove property (T) for an even larger group St_n(R)" (read at source). `R_l` is
  finitely generated. **It matches.**
- **Part 2.** `c ↦ x_12(θ(c))` is a homomorphism by (R1). It is injective because its composite to `E_N(R_l)` is
  `c ↦ e_12(θ(c))`, and `θ` is injective: its composite with `R_l → R̄_l` is. **Correct.**
- **Part 1.** `θ : Z_(l) → eR_le` lifting the injective `θ` of `rf-resolvent-ring-has-z-localized-corner`. It is a
  lane construction in the proof route, which I did not review. It carries no citation.

## (2) Steinberg residual finiteness forces ring residual finiteness

- `I = {r : ρ(x_12(r)) = 1}` is a finite-index additive subgroup.
- Spreading to every `x_ij(r)`, `r ∈ I`: Milnor, *Introduction to algebraic K-theory*, §9, treats `St(Λ)` for an
  arbitrary associative ring. The conjugation formulas for `w_ij = x_ij(1)x_ji(−1)x_ij(1)` are standard there, and
  signs don't matter for a kernel.
- **R2 (optional).** The Weyl elements are unnecessary. `x_1j(r) = [x_12(r), x_2j(1)]`,
  `x_k2(r) = [x_k1(1), x_12(r)]`, and so on (the six identities in
  `st-n-of-ring-quotient-adds-one-relator-per-ideal-generator`), give `x_ij(r) ∈ ker ρ` from the Steinberg relations
  alone, for `N >= 3`. The Milnor citation can then be dropped.
- `rs, sr ∈ I` via `[x_13(·), x_32(·)]`, so `I` is a two-sided ideal of finite index.
- `ρ` factors through `St_N(R/I)`.
- Conclusion: if `St_N(R)` is residually finite, then `R` is residually finite. **Correct.**

## (3) Wording against the sources

- **Rauzy, arXiv:2002.02540 (v1 6 Feb 2020, v2 17 Mar 2021), abstract**, verbatim: "for a finitely generated
  residually finite group, having solvable word problem is not a sufficient condition to be a subgroup of a finitely
  presented residually finite group. The obstruction is given by a residually finite group with solvable word
  problem for which there is no effective method that allows, given some non-identity element, to find a morphism
  onto a finite group in which this element has a non-trivial image."
  - The node's "solvable WP plus effective RF; Rauzy's counterexample fails the second" matches.
- **Kharlampovich–Myasnikov–Sapir, arXiv:1204.6506 (v1–v5), abstract**, verbatim: "The groups are solvable of
  class 3." This matches "the KMS groups themselves are soluble of class 3".
- **The §1.1.7 question.** The repo node `rf-higman-embedding-for-decidable-groups` quotes it: "whether every
  finitely generated residually finite group with solvable word problem embeds into a finitely presented residually
  finite group". I did not re-read §1.1.7 here.
- **R3 (attribution).** KMS ask the unrestricted question. The restriction to effectively residually finite groups
  is the lane's own reformulation after Rauzy. The node's sentence ("restricted to effectively residually finite
  groups … would settle") reads correctly. Keep it from being cited as "KMS Question 1.1.7 (effective form)". Call
  it "the effective-RF form of the KMS question, left open by Rauzy".
- **Bounded search.** "No source settling the restricted form" is the lane's bounded search. It is not reviewed
  here.

## Not reviewed

- The construction and residual finiteness of the Euler lamplighter `G_l` (parts 1–5): proof-gap matters.
- `fg-metabelian-groups-have-roots-at-finitely-many-primes`, used for derived length 3.
