# Swarm log: `zaremsky-2-10-braided-v-hopfian` (Zaremsky Problem 2.10), 2026-09-16

The agent was `swarm-zaremsky-2-10-braided-v-hopfia`. It locked the hole
`some-quotient-of-braided-v-is-not-finitely-presented`.

The outcome is a **complete argument for the hole** (UNREVIEWED). `bV` has `2^aleph_0` normal subgroups and an
infinite strictly ascending chain of normal subgroups. So `bV` fails max-n, and some quotient of `bV` is not
finitely presented.

With the ESTABLISHED `braided-thompson-v-is-hopfian`, the existing route
`zaremsky-2-10-by-hopfian-and-non-fp-quotient` now closes the root. Problem 2.10 is answered: braided V is Hopfian,
and not every quotient of braided V is finitely presented.

The full proof is in `research/artifacts/braided-v-continuum-normal-subgroups-2026-09-16.md`.

## 1. Graph changes

New claims:

- `braided-v-normal-subgroups-from-three-strand-deletions`, with direct-proof route `-proof` (Theorem A).
- `b3-has-continuum-many-normal-subgroups-in-pb3-commutator`, with direct-proof route `-proof` (Lemma B and
  Corollary C).
- `braided-v-has-continuum-many-normal-subgroups`, with route `-proof` requiring the two claims above.

New route into the hole: `some-quotient-of-braided-v-is-not-fp-via-neumann`. It requires
`braided-v-has-continuum-many-normal-subgroups` and proves B. H. Neumann's lemma in its body.

Edited node: `every-quotient-of-braided-v-is-finitely-presented` gains
`refuted_by: [some-quotient-of-braided-v-is-not-finitely-presented]`. The README says "A false claim owns its
refutation link". This also invalidates the dead answer route `zaremsky-2-10-by-hopfian-and-fp-quotients`
automatically.

## 2. The idea in one paragraph

Zaremsky (arXiv:1403.8132v2 §4) shows that normal subgroups of `V_br` inside `P_br` are the same as sequences
`G_n ◁ B_n` with `clone_k(PB_n) ∩ G_{n+1} = clone_k(G_n)`. His m-loose examples demand that all `m`-strand
deletions be *trivial*.

Instead, prescribe that all 3-strand deletions land in a given normal subgroup `M ◁ B_3`, and also require
`p ∈ [PB_n, PB_n]`. Conjugation is handled because deletion commutes with stacking (`beta ∈ B_3`). Coherence at
generic triples is Zaremsky's `pi_{S(k)} ∘ clone_k = pi_S`. At the degenerate triples containing both clones,
`pi_{S'} ∘ clone_k` factors through `PB_2 = Z`, which kills commutators; this is why `[PB_n, PB_n]` is imposed.
Completeness uses the left-inverse "delete one clone".

The 3-strand stage of `N_M` is exactly `M`, so `M -> N_M` is injective. `B_3` has continuum many normal subgroups
inside `PB_3''`. They correspond to `S_3`-submodules of `Q_2 = PB_3''/[PB_3, PB_3''] = F''/[F, F''] = H_2(F/F'')`.
Here `F = F_2`, and `H_2` of the free metabelian group of rank 2 contains `(Λ^2 Z[Z^2])_{Z^2} = Z^(aleph_0)` by LHS.

## 3. Where earlier attempts died, and why this escapes

Per the hole's Attempts, each graded piece `gamma_c/gamma_{c+1}` has only countably many `V`-invariant subgroups,
so an uncountable family must mix depths. The `N_M` do exactly that: no `N_M` contains any `gamma_c(P_br)`,
because `F/F''` is not nilpotent (artifact §6.2). This is consistent with the ESTABLISHED
`braided-v-max-n-above-lower-central-terms`.

## 4. Alternative route not promoted (verbal subgroups)

1. For any set of group words `W`, the verbal subgroups `W(PB_n)` form a complete coherent sequence of normal
   subgroups of the `B_n`.
   - `W(PB_n)` is characteristic in `PB_n ◁ B_n`, so it is normal in `B_n`.
   - `clone_k` maps `W(PB_n)` into `W(PB_{n+1})`.
   - Completeness follows from the left-inverse retraction `delete clone k+1`.
2. The 3-strand stage is `W(PB_3) = W(F_2) × W(Z)`, and `F_2` is a retract of `PB_3`. So distinct verbal
   subgroups of `F_2` give distinct normal subgroups of `V_br`.
3. An infinite independent system of 2-variable identities would give an ascending chain, and continuum many
   subsystems.
   - Such systems are attributed to S. I. Adian (1970). The specific form (powers of commutators of large powers)
     was recalled but **not verified** against a primary source this session. The zbmath.org web pages and
     mathnet.ru returned 403, and the zbMATH API records gave bibliographic data only.
   - The route stays in notes because the self-contained `N_M` construction needs no such input.
   - It would give another proof (and a different family of normal subgroups) once a verified independent
     2-variable system is imported.

## 5. Other dead ends and side checks

- A preliminary attempt to obstruct finite presentability of `bV/[P_br, P_br]` found no obstruction. It looked at
  coinvariants of homology of the abelian kernel. Details were not retained, and the question stays open (artifact
  §6.4).
- `bin/cairn status <id>` is invalid usage: `status` takes no id.

## 6. Literature gate (checked 2026-09-16)

- **Zaremsky, arXiv:1403.8132v2.** The LaTeX source was fetched and §4 read verbatim:
  - Prop 4.1: subgroups of `P_br` correspond to complete coherent families.
  - Lemma 4.2: normality in `F_br`.
  - Equation (CC).
  - Lemma 4.3: `V_br`-normal if and only if each `G_n ◁ B_n`.
  - Lemma 4.4: m-loose sequences, with `pi_{S(k)} ∘ kappa_k^n = pi_S`.
  - Question 4.7 (Hopfian?) and Prop 4.8 (`P_br` is not Hopfian).
  - Numbering is the compiled per-section counter. The Introduction states that `V_br` and `F_br` are finitely
    presented.
- **Zaremsky, *Some open problems*, version of July 12, 2026.** Fetched 2026-09-16. Section 2, Problem 10 is
  still unmarked, so it is open.
- **arXiv API, 2026-09-16.** The newest hit for `all:"braided Thompson"` is arXiv:2503.11594, which is on a
  different topic. The following queries returned no relevant hits:
  - `abs:"braided Thompson" AND abs:"normal subgroups"`: only 1403.8132;
  - `abs:"braided" AND abs:"Hopfian"`: only virtual, welded and surface braid papers;
  - `all:"braided V"` submitted 2024–2026: none;
  - `abs:"Thompson" AND abs:"max-n"`: none.
- **Brady–Burillo–Cleary–Stein**, arXiv:math/0603548 (Publ. Mat. 52 (2008)). Only the arXiv abstract was read:
  finite presentations of `BF`.
- **Kourovka Notebook**, arXiv:1401.0300 (LaTeX source, current version). It was searched for Adian's
  independent systems, and the exact form was not found.
- **Adian–Atabekyan**, arXiv:1811.07167, *Central extensions of free periodic groups*. It was checked for the
  2-variable identities, and the needed statement was not extracted.
- The zbMATH API records for Adian 1970 and the EoM article "Variety of groups" were consulted for the verbal
  route only. The promoted proof does not use them.

## 7. Weakest steps, for a referee

1. Theorem A, steps (ii)/(iv): the coherence equation at degenerate triples `S' ⊇ {k, k+1}`, and the claim that
   membership in `Th(G_*)` is invariant under expansion. This gives `N_M ∩ PB_{T_3} = M`.
2. Lemma B, LHS step: the identification `A = F'/F'' ≅ Z[Z^2]`, the vanishing of `E_{2,1}` and `E_{3,0}`, and
   `E^inf_{0,2} = H_2(A)_{Z^2}` embedding in `H_2(F/F'')`.

A sanity cross-check is known from the literature: the Schur multiplier of the free metabelian group of rank 2 is
free abelian of infinite rank. This was **not verified** from a source this session and is not used.

## 8. Open follow-ups

- Is `V_br/[P_br, P_br]` finitely presented? It is an extension of `V` by `C_c(Y, Z)`.
- Is `V_br/N_M` finitely presented for a specific `M`, for example `M = [PB_3, PB_3'']` or `M = 1`?
- Does `F_br` satisfy the Hopf property (the `F_br` half of Zaremsky's Question 4.7)?

## Referee (2026-09-16)

Adversarial referee and landing agent for this lane.

**What I checked.**

- Read every listed file in full, the committed nodes they touch (`zaremsky-2-10-braided-v-hopfian`, both answer
  routes, `some-quotient-of-braided-v-is-not-finitely-presented`, `every-quotient-of-braided-v-is-finitely-presented`,
  `braided-thompson-v-is-hopfian` via `cairn why`), and `git status` for unlisted files. None were found.
- **Zaremsky source.** I re-fetched arXiv:1403.8132v2 e-print (`normal_subgroups_BF_BV.tex`) and compared §4
  against the artifact's quotes: Prop 4.1, Lemma 4.2, Equation (complete coherent), `Th(G_*)`, Lemma 4.3 and its
  displayed conjugation, the `pi_{S(k)} ∘ kappa_k^n = pi_S` identity in the proof of Lemma 4.4, Question 4.7,
  Prop 4.8. All quotes match. The bibliography confirms Brin 2007 (J. Group Theory 10) and Dehornoy 2006
  (Adv. Math. 205) for finite presentability.
- **Problem status.** Re-fetched https://zaremsky.github.io/open_problems.pdf: dated July 12, 2026; Section 2,
  Problem 10 is still listed without any update note. arXiv API (2026-09-16): newest `all:"braided Thompson"` hit
  is still arXiv:2503.11594; `abs:"maximal condition on normal subgroups" AND abs:Thompson` and `abs:"braided V"`
  give nothing relevant; `abs:braided AND abs:Hopfian` gives only virtual/welded/surface braid papers. No prior
  resolution found.
- **Theorem A, line by line.** Normality via (D1); coherence (⊇) at generic triples via (D2) and at degenerate
  triples via (D3); completeness (⊆) via the left inverse (D4); well-definedness of `Th(G_*)` via common expansions
  and the fact that every representative of an element of `P_br` is `(T, p, T)` with `p` pure; normality in `V_br`;
  `G_3(M) = M`. No gap found. The key design choice (imposing `p ∈ [PB_n, PB_n]` so that degenerate triples
  containing both clones are automatically fine) is exactly what makes (CC) hold.
- **Computation.** `experiments/zaremsky-2-10-strand-deletion-checks-2026-09-16/strand_checks.py` tests (D1), (D2),
  (D3), "commutators die on degenerate triples" and (D4) on 150 random pure braids with `n = 3..5`, random cloned
  strand and random conjugators. 3-strand equalities use the unreduced Burau representation (faithful on `B_3`),
  and (D4) uses the Artin action on `F_n`. Result: 0 failures, and 90 of the tested commutators had nontrivial
  3-strand projections, so the (D1) test is not vacuous. A first run of my own script had a wrong Burau matrix and
  produced spurious failures; I caught it with the sanity asserts now in the script (inverse, braid relation,
  nontrivial commutator) before drawing any conclusion.
- **Lemma B.** Checked `PB_3 = F × <Delta^2>` (`pi_{12}(Delta_3^2) = A_12`), Hopf's formula with `R = F'' ≤ F'`,
  `F'/F'' ≅ Z[Z^2]` as `H_1` of the square grid (`d_2` injective, no 3-cells), `E^2_{2,1} = H_2(Z^2; Z[Z^2]) = 0`,
  `E^2_{3,0} = H_3(Z^2) = 0`, and the edge-map identification of `E^inf_{0,2}` with the image of `H_2(A)`. The
  free action of `Z^2` on 2-subsets and the coinvariant computation `Z^((Z^2 \ 0)/±)` are correct. This agrees
  with the classical fact (not re-fetched here, so used only as corroboration) that the multiplier of the rank-2
  free metabelian group is free abelian of infinite rank.
- **Corollary C and Theorem D.** Chain argument, Maschke decomposition, injectivity of `J -> P_J`, the union
  argument, the full proof of B. H. Neumann's lemma, and the countability count. All correct.
- **Cairn discipline.** Ids within budget; the two `requires: []` routes are complete direct proofs whose
  literature inputs are either classical (Hopf, LHS, Maschke, Artin combing) or read verbatim and re-derived
  (Zaremsky §4). The root forbids `requires: []` routes into it, and none was written: the root closes through the
  existing `zaremsky-2-10-by-hopfian-and-non-fp-quotient`. Adding `refuted_by` to
  `every-quotient-of-braided-v-is-finitely-presented` follows the README ("a false claim owns its refutation link")
  and is necessary for the graph to record the "no" answer. Duplicate search (`search --similar` on all three new
  claims) found no near-duplicate; the `distinct_from` entries are accurate.

**What I changed.**

- `some-quotient-of-braided-v-is-not-fp-via-neumann`: replaced "Clearly `J ≤ K`" and the terse left-inverse step
  with explicit computations.
- `braided-v-has-continuum-many-normal-subgroups-proof`: added step 5 justifying the `F_br` sentence of the claim
  (it was asserted in the claim but not argued in the route).
- `braided-v-normal-subgroups-from-three-strand-deletions-proof`: replaced "Monotonicity is immediate" with the
  one-line argument.
- Artifact: status line and novelty line updated from UNREVIEWED to "refereed by the swarm landing referee",
  pointing here.
- Added the replayable check script under `experiments/`.

**Verdict.** Sound. Landed with small fixes. Zaremsky Problem 2.10 answer recorded by the graph: braided V is
Hopfian (earlier, reviewed PASS) and some quotient of braided V is not finitely presented (this lane). Still open
and not claimed: finite presentability of `V_br/[P_br, P_br]` or of any specific `V_br/N_M`; Hopficity of `F_br`.
The notes' §4 verbal-subgroup route stays unpromoted (Adian's identities unverified), which is correct.
