---
rg: 2
id: seeded-recursively-presented-groups-have-solvable-word-problem
kind: claim
title: A recursively presented group with an effectively closed subshift that has an isolated point with trivial stabilizer has solvable word problem, uniformly in the data; so every finitely presented group with a seed, rigid or not, has solvable word problem and its seed SFT has decidable language
distinct_from:
  seeds-never-survive-marked-approximation: that proves seeds are relative isolation (fp ⇔ relatively isolated) and leaves open whether fp plus a seed forces a solvable word problem; this answers that question yes, with the certificate for w ≠ 1 it asked for.
  decidable-groups-embed-in-rigid-sft-compactification-groups: that is the open (SEED) gate, which assumes the input decidable; this shows the other direction is automatic, since every group carrying a seed over a recursively presented group is decidable.
  heisenberg-rigid-seed-certifies-only-the-malcev-normal-form: that measures the word-problem complexity certified by one explicit seed; this proves every seed certifies a decision procedure, by one uniform search.
---

**ESTABLISHED** (lane proof, elementary; bh-invent-10, 2026-09-18; not independently reviewed). Route:
`seeded-groups-solvable-word-problem-proof`. No priority is claimed. The argument is the standard fact that a
`Π^0_1` singleton is computable. It is the seed analogue of Jeandel's theorem (arXiv:1501.06831, abstract read):
a finitely presented group with a strongly aperiodic SFT has decidable word problem. Seeds are not aperiodic
(their boundaries have fixed points), so that theorem does not apply to them.

## Statement

Let `Γ = ⟨S | R⟩` be finitely generated with `R` recursively enumerable, and let `Y ⊆ A^Γ` be an effectively closed
subshift, meaning its forbidden patterns on balls form a recursively enumerable set. The action is
`(g.x)(h) = x(g^(-1) h)`. Suppose `y_* ∈ Y` and `p` is a pattern on a ball `B_(R_0)` with:
- (S1) `{y ∈ Y : y|_(B_(R_0)) = p} = {y_*}`;
- (S2) `Stab(y_*) = 1`.

Then:
1. **The seed point is computable.** Some algorithm, given a word `u` in `S^(±1)`, outputs `y_*(ū)`.
2. **The word problem is solvable.** A word `w` represents `1` iff `y_*(w^(-1) f) = p(f)` for every `f ∈ B_(R_0)`.
3. **Uniformity.** One algorithm works for all data: the finite ball `B_(max(r,R_0))` of `Γ` as a labelled graph,
   an enumeration of `R`, an enumeration of the forbidden patterns, and `p`.
4. **Decidable language.** If in addition `Y` is the orbit closure of `y_*` (condition (C2) of an SFT
   compactification), the language `L(Y)` is decidable.

Density (C2) is used only in part 4. No rigidity, finite type or minimality is used.

## Consequences

- **Answer to the open question of `seeds-never-survive-marked-approximation`.** Finite presentation plus a seed
  forces a solvable word problem.
  - The certificate for `w ≠ 1` is a finite stage of the compactness search at which every surviving assignment
    disagrees with `p` somewhere on `w^(-1) B_(R_0)`.
  - With that node, this completes the parallel with isolated groups. There, finite presentation plus finite
    discrimination gives a solvable word problem (Cornulier–Guyot–Pitsch, recalled). Here, a seed plays the role
    of finite discrimination for both conclusions.
- **Seeds need decidable groups.** A finitely presented group with unsolvable word problem carries no seed, on
  any effectively closed subshift. So `𝒞` contains, among recursively presented groups, only decidable ones.
- **(D′) is automatic.** The synthesis remark "seed(Λ₀) + WP ⇒ (D′)" loses its WP hypothesis for recursively
  presented `Λ₀`, by part 4.
- **For CAP (SYNTHESIS v6 gate 1).** Every seed over a recursively presented group runs the same uniform
  algorithm. So CAP is a statement about the running time of that one search on rigid seeds, and nothing else.
  - Decidability itself can never be the cap.
  - A proof of CAP must bound the refutation depth of the search, that is, how far the SFT must be unrolled
    before a wrong value at `u` is refuted.
  - A refutation of CAP must make that depth grow faster than any fixed class allows.

## Lesson for general BH

A seed is a finite proof of its own uniqueness.
- Its point is the only member of an effectively closed class, so it is computable. Trivial stabilizer then turns
  "is this word trivial?" into "does the seed pattern reappear there?".
- So a seed carries the word problem **in its forcing**: every word is decided by unrolling the constraints from
  the origin.
- The difficulty of general BH on the seed route is therefore not decidability but the *cost of forcing*. A rigid
  seed must let that cost be as large as the input's word problem demands.
