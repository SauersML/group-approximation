---
rg: 2
id: artin-2x2-dead-joins-sigma1-iff-k-q-odd-family
kind: claim
title: "Sigma^1 at the dead character of every 2x2 dead-join Artin group: membership holds exactly for the odd K_q family (three half-labels 2, the fourth odd)"
distinct_from:
  artin-k4-odd-family-dead-characters-lie-in-sigma1: that proves membership for the odd K_q family; this proves non-membership for every other 2x2 dead join, so that family is exactly the membership locus of the class
  artin-sigma1-dead-edge-ring-obstruction: that needs a ring in which the dead-edge sums vanish; this uses matrix modules in which they are only singular, and for halves (2,q,2,p) with gcd(q,p) = 1 no nonzero ring witness exists at all
  artin-k4-dead-cut-admits-no-nonzero-dead-edge-ring: that shows the ring method is empty for K_3; this decides all 2x2 dead joins
  artin-sigma1-is-connected-dominant-living-subgraph: that is the conjecture for all Artin groups; this decides it on the 2x2 dead joins, where it fails exactly on the odd K_q family
  zaremsky-1-06-bns-invariant-of-every-artin-group: that is the whole problem; this computes Sigma^1 at the dead characters of one four-parameter class of Artin groups
artifacts:
  - experiments/artin-join-sigma1-2026-09-17/general_constructions.py
  - experiments/artin-join-sigma1-2026-09-17/general_constructions.log
  - experiments/artin-join-sigma1-2026-09-17/certify_witness.py
  - experiments/artin-join-sigma1-2026-09-17/certify_witness.log
---

**Setting (2x2 dead join).** Let `Γ` be the complete graph on `a, b, c, e` with
`l(ab) = l(ce) = 2` and even cross labels `l(xy) = 2 h_xy`, `h_xy >= 2`, for
`x ∈ {a, b}`, `y ∈ {c, e}`. Write the halves as `(h_ac, h_bc, h_be, h_ae)`; the cross
edges form the 4-cycle `a–c–b–e–a`. Let `χ(a) = χ(b) = 1`, `χ(c) = χ(e) = -1`.

All four cross edges are dead, and `±χ` are the only dead characters of `A_Γ` up to
positive scaling (a dead cross edge forces `χ(x) = -χ(y)`). The Σ¹-conjecture
(`artin-sigma1-is-connected-dominant-living-subgraph`) predicts `[±χ] ∉ Σ^1` for
every choice of halves.

**Claim.** For every choice of halves the following are equivalent:
1. `[χ] ∈ Σ^1(A_Γ)`;
2. `[-χ] ∈ Σ^1(A_Γ)`;
3. `ker χ` is finitely generated;
4. exactly three of the four halves equal `2`, and the fourth is odd.

Condition 4 describes `K_q` with `q` odd (`artin-k4-odd-family-dead-characters-lie-in-sigma1`),
up to the symmetries of the square. In every other case there is a representation
`ρ : A_Γ -> GL_n(F)`, `F` a cyclotomic field, whose `χ`-twisted Alexander module
`H_1(A_Γ; F(t)^n)` has positive `F(t)`-rank, and this forces `[±χ] ∉ Σ^1`.

**What it shows for Problem 1.6.**
- On this class the Σ¹-conjecture is right except on the odd `K_q` family. So within
  the class the counterexamples are exactly that family, and a corrected formula
  must see the arithmetic of the half-labels (here: "three 2s and an odd"), not only
  the living subgraph. Among the claims recorded here, this is the first class with
  a dead cut where `Σ^1` is decided for all label choices and the answer differs from
  the conjecture's (literature not searched beyond the sources cited in the graph).
- The witnesses are all explicit, and small:
  - a 2-dimensional representation when some vertex has both halves `>= 3`;
  - a `p`-dimensional signed permutation representation for halves `(2, q, 2, p)`
    with `3 <= q < p`;
  - a 1-dimensional one in the other cases.
- Non-membership here is not always detected by dead-edge rings. For halves
  `(2, q, 2, p)` with `gcd(q, p) = 1` (for example `(2, 3, 2, 5)`), every ring
  witness is the zero ring (proof, Remark R1). Yet `[±χ] ∉ Σ^1`. So the
  ring-witness criterion is strictly weaker than non-membership, even among the
  non-members. The right invariant is the twisted Alexander rank over all
  finite-dimensional representations.

Proof: `artin-2x2-dead-joins-sigma1-iff-k-q-odd-family-proof`.
