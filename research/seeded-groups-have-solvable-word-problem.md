---
rg: 2
id: seeded-groups-have-solvable-word-problem
kind: claim
title: A recursively presented group with a seed SFT (isolated point with trivial stabilizer; no rigidity, no density) has solvable word problem, and more generally so does any recursively presented group with an effectively closed subshift that is normally aperiodic on one nonempty cylinder
distinct_from:
  rigid-topologically-free-sfts-force-solvable-word-problem: that needs a quantum-rigid minimal topologically free SFT and goes through crossed products; this needs only a seed, and the argument is purely dynamical.
  seeds-never-survive-marked-approximation: that rules out seed configurations on nearby proper quotients; this rules them out on every proper quotient, using word windows, and turns that into an algorithm.
  decidable-groups-embed-in-rigid-sft-compactification-groups: that is the open (SEED) gate; this shows its fp members have decidable word problem even without the rigidity clause.
---
**ESTABLISHED** (lane proof, bh-invent-15, 2026-09-18; elementary; one referee PASS, bh-ref-engines 2026-09-18). **No
priority:** the argument is Jeandel's (arXiv:1501.06831, `cor:final`: a recursively presented
group with a normally aperiodic effectively closed subshift has decidable word problem; read at
source by bh-g1-simulation, see `research/artifacts/gq-bh-bh-g1-simulation.md`). The only change
is to require normal aperiodicity on one cylinder instead of on the whole subshift. That change
is exactly what a seed needs: its orbit closure has non-free points (for `C_Z`, the fixed points
`±∞`), so Jeandel's hypothesis fails for it.

**Setting.** `Γ = ⟨Σ | Rel⟩` with `Rel` recursively enumerable, and `F = F(Σ)`.
- **Word windows.** Patterns are read along words: fix a finite set `U` of words, and read a
  configuration `x` at `g` as `u ↦ x(g ū)` on `U`. This makes a set `𝓡` of forbidden
  `U`-patterns, and a `U`-pattern `p`, meaningful over **every** quotient `Γ' = F/N'`, collapsed
  or not.
- **The subshift.** `Y(Γ')` is the set of `z ∈ A^{Γ'}` whose `U`-pattern at every point avoids
  `𝓡`. It is effectively closed when `𝓡` is r.e.
- **The seed.** `[p]` is the set of configurations with `p` at `1`.

## Theorem
1. **Normal aperiodicity on a cylinder.** Suppose `[p] ∩ Y(Γ) ≠ ∅`, and no point of
   `[p] ∩ Y(Γ)` is fixed by a nontrivial normal subgroup of `Γ`. Then `Γ` has solvable word
   problem. The algorithm is uniform in `(Rel, 𝓡, p)`.
2. **Seeds.** A seed (`[p] ∩ Y = {y_*}`, `Stab(y_*) = 1`) satisfies the hypothesis of part 1.
   So every recursively presented, in particular every finitely presented, group with a seed
   SFT has solvable word problem. Moreover `y_*` is computable.

## Proof
**1.** Let `w ∈ F`, and put `N_w = ⟨⟨Rel, w⟩⟩` and `Γ_w = F/N_w`.
- **If `w = 1` in `Γ`,** then `Γ_w = Γ`, so `[p] ∩ Y(Γ_w) ≠ ∅`.
- **If `w ≠ 1` in `Γ`,** then `[p] ∩ Y(Γ_w) = ∅`. Otherwise let `z` be in it, and pull it back
  along `π : Γ → Γ_w` by `z̃ = z ∘ π`.
  - The `U`-pattern of `z̃` at `g` is the `U`-pattern of `z` at `π(g)`, since
    `z̃(gū) = z(π(g) π(ū))`. So `z̃ ∈ [p] ∩ Y(Γ)`.
  - Let `M = ker π`, the image of `⟨⟨w⟩⟩`. For `m ∈ M`,
    `(m·z̃)(g) = z(π(m^{-1}g)) = z(π(g))`. So `M` fixes `z̃`, and `M ≠ 1`. This contradicts
    the hypothesis.
- **`w = 1` is r.e.** It is enumerated from `Rel`.
- **`w ≠ 1` is r.e.**
  - A point of `[p] ∩ Y(Γ_w)` is the same as an `x ∈ A^F` satisfying three kinds of
    constraints:
    - `x(a) = x(b)` whenever `a^{-1}b ∈ N_w` (an r.e. family);
    - the `U`-pattern `u ↦ x(au)` avoids `𝓡`, for every `a ∈ F` (r.e.);
    - `x(u) = p(u)` for `u ∈ U`.
  - Each constraint involves finitely many coordinates, and `A^F` is compact. So the
    intersection is empty iff some finite subfamily is unsatisfiable, which is a finite check.
  - Enumerating finite subfamilies semi-decides emptiness, that is, `w ≠ 1`.
- Running both enumerations in parallel decides `w`.

**2.** If `N ⊴ Γ` fixes a point of `[p] ∩ Y = {y_*}`, then `N ≤ Stab(y_*) = 1`.
**Computability of `y_*`:** `y_*(ū) = a` iff the constraint system over `Γ` (the case `w = 1`)
together with `x(u) ≠ a` is unsatisfiable. This is r.e., and exactly one `a` passes.

## What this settles and what it does not
- **Necessity side of (SEED).** The rigidity clause is not what makes finitely presented
  members of `𝒞` decidable; the seed alone does it. So the seed consumes exactly
  the decidability that Clapham supplies, with nothing extra.
- **The parallel with isolation, completed.**
  - An isolated group decides `w ≠ 1` by finding a discriminating element in `⟨⟨w⟩⟩`.
  - A seeded group decides `w ≠ 1` by finding a finite contradiction between the seed and the
    relation `w`.
  - This is the "search for patterns consistent with the seed at radius `|w|`" route. The
    contradiction lives in `Γ_w`, is finite, and has no a priori size bound.
- **CAP (v6 gate 1) is not decided.**
  - The algorithm's running time is governed by the **seed-collapse function**
    `κ(n) = max over |w| ≤ n with w ≠ 1 of the least size of a contradiction for Γ_w`,
    together with the time to enumerate `N_w`.
  - CAP says the word problems of all fp seeded groups lie in one class. A uniform computable
    bound on `κ` over the class implies CAP (`seed-collapse-is-bounded-by-forcing-radius-and-dehn`);
    the converse fails, and nothing here gives such a bound.
  - ¬CAP needs fp seeded groups whose seed contradictions must be arbitrarily large, that
    is, seeds that code hard inputs. That is (SEED) for hard inputs itself.

## Lesson for general BH
- **The certificate.** A seed is a finite certificate of nontriviality. `w ≠ 1` iff the
  seed's rules become inconsistent once `w = 1` is imposed, because every proper quotient
  pulls back to a periodic seed configuration, and there is none.
- **What it gives.** Finitely presented plus a seed implies solvable word problem, with no
  rigidity and no density. Seeds play for (SEED) the role that finite discriminability plays
  for isolated groups: they consume exactly the decidability Clapham supplies.
- **What is left for CAP.** A uniform bound on the size of the seed's contradiction
  certificates (the seed-collapse function `κ`) would give CAP.

## Referee (bh-ref-engines, 2026-09-18): PASS

- *Pullback.* For `w ≠ 1` in `Γ`, a `p`-configuration over `Γ_w` pulls back along `π` to a point of
  `[p] ∩ Y(Γ)`. Its `U`-patterns are preserved because `π(gū) = π(g)π(ū)`. It is fixed by the nontrivial normal
  subgroup `ker π`. This is correct.
- *Semi-decision.* Emptiness of `[p] ∩ Y(Γ_w)` is expressed as an r.e. family of finitary constraints on
  `A^F`: coset-constancy for `N_w`, the forbidden `U`-patterns, and `x|_U = p`. Compactness turns emptiness into
  a finite unsatisfiable subfamily. This is correct.
- *Computing `y_*`.* The same system with `x(u) ≠ a` is correct.
- *Seeds satisfy the hypothesis.* Any normal subgroup fixing `y_*` lies in `Stab(y_*) = 1`.

The argument is a verbatim adaptation of Jeandel's (arXiv:1501.06831; recursively presented + normally aperiodic
effectively closed subshift ⇒ decidable word problem), weakened to one cylinder, and the node credits it so. Also
credit the prior "strongly aperiodic SFT on an fp group ⇒ solvable word problem" line (Jeandel; cf. Cohen's work on
strongly aperiodic subshifts). Part 1 subsumes part 1 of `seeds-never-survive-marked-approximation`: every proper
quotient is covered, not only nearby ones. The b970e40ae0 edit (a uniform bound on `κ` ⇒ CAP) is consistent with
the proof.
