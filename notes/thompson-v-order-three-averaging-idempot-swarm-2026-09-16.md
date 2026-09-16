# thompson-v-order-three-averaging-idempotent-is-full: swarm notes, 2026-09-16

Lane `swarm-thompson-v-order-three-averagi`. Outcome: **reduction**. The target is not solved. It is shown
equivalent to a representation statement about `V` alone, with consequences, a support filter and finite
checks.

Full proofs: `research/artifacts/thompson-v-weakly-finite-representations-2026-09-16.md`.
Script: `experiments/thompson-v-order-three-averaging-idempot-swarm-2026-09-16/verify_host_and_blocks.py`,
output in `output.txt` in the same directory (checks C1–C5, all pass, a few seconds, seed 20260916).

## Setup

- `h = (00, 01, 1) -> (01, 1, 00)` in `V`, `e_h = 1 + h + h²` in `F_2[V]`. Target: `c e_h b = 1`.
- `g = (0, 10, 11) -> (10, 11, 0)`, the permutation unit `s_2 t_1 + s_3 t_2 + s_1 t_3` of the binary cyclic
  corner of `research/artifacts/binary-cyclic-corner-complement-states-2026-09-12.md` ([CS]).
- `k = (00, 01, 1) -> (0, 10, 11)` gives `k h k^(-1) = g`, so the target is `c e_g b = 1` in `F_2[V]`.
- `V` is a host for Theorem B of [CS]: it contains `g` and the nine-cylinder units `π_M`, and it is stable
  under the halving map `D(x) = Σ s_i x t_i`. This is also Section 4 of
  `research/artifacts/gk3-binary-fullness-2026-09-14.md`.

## What was proven (on paper)

1. **Theorem W_V** (artifact Section 2). The target holds iff every group homomorphism from `V` into the unit
   group of a weakly finite ring of characteristic two is trivial. It is also equivalent to the same with
   "directly finite", to `T_V = f F_2[V] f` having no nonzero weakly finite image, and to `φ(h) = 1` for every
   unital `φ` into a weakly finite (or directly finite) ring.
   - Direction (d) => (a) uses Theorem C (`rank-condition-rings-have-weakly-finite-images`), Theorem B of
     [CS] at host `V`, and Lemma W.2 of `research/artifacts/binary-weakly-finite-representations-2026-09-12.md`
     at host `V`.
   - Direction (a) => (d) uses only size-one direct finiteness and simplicity of `V`.
   - New claim `thompson-v-has-no-weakly-finite-char-two-representation`, with routes in both directions.
2. **Uniformity** (Corollary 3.1). If any odd-order finite subgroup `K` has full `e_K`, the target holds. If the
   target holds, `e_x` is full for every `x` of order three in `V`, through the diagonal embedding `θ` built
   from the canonical partition of `⟨x⟩`.
3. **Ascent** (Corollary 3.2). The target implies `binary-cyclic-averaging-idempotent-is-full-on-leavitt-units`
   (route `binary-cyclic-corner-fullness-ascends-from-thompson-v`). The V-representation claim implies the
   `R^x`-representation claim.
4. **Rank gate** (Corollary 3.3). The V-representation claim implies
   `thompson-v-has-no-nontrivial-f2-rank-model` (route `thompson-v-rank-gate-from-no-weakly-finite-rep`).
5. **Dead hosts** (Corollary 3.4). No nontrivial characteristic-two representation of `V` exists into:
   - commutative rings;
   - division rings, since `C_3²` cannot sit in the units of a finite field;
   - rings whose nilpotents have bounded index, since the `2^m`-cycles of `V` become unipotent.
6. **Support filter** (Proposition 4.1), valid in `F_2[Γ]` for every group `Γ`, from [DHJ] Proposition 4.21:
   - `|b|` and `|c|` are odd and at least `3`;
   - `(|c|, |b|) != (3, 3)`;
   - `|c| = 3` forces `|e_h b| >= 13`, and `|b| = 3` forces `|c e_h| >= 13`;
   - `|c| = 5` forces `|e_h b| != 5`, and `|b| = 5` forces `|c e_h| != 5`.

## Finite checks ([EXP])

- C1: `h³ = g³ = 1`.
- C2: `k h k^(-1) = g`, on all words of length 12.
- C3: `D(g)` commutes with `g`, and `⟨g, D(g)⟩` translates the nine cylinders freely.
- C4: `θ_U` is multiplicative on random products of cylinder swaps (80 pairs, two splittings, 4000 length-40
  words), and `θ_U(h)` is the 3-cycle.
- C5: the `F_2[C_3²]` block identities of Lemma W.2, with an explicit inverse in the block.

## Approaches tried, and exactly where each dies

- **Theorem W alone.** It is an equivalence, so it decides nothing without a weakly finite target.
- **Refuting the representation claim with standard hosts.** Commutative rings, division rings and
  bounded-nilpotence rings are all excluded (Corollary 3.4). What remains is noncommutative rings with
  nilpotents of unbounded index: rank ultraproducts (soficity-type questions, open for `V`) and group algebras
  (stable finiteness of `F_2[V]`, open).
- **Proving the representation claim through the evaluation.** `π(h) != 1` in `L_(F_2)(1,2)`. So if
  `P = π(F_2[V])` were directly finite, the target would be false. The Leavitt witness `b_0 = s0 + s10 + s11`,
  `c_0 = t0 + t10 + t11` is balanced, so Lemma 3.1 of `research/artifacts/thompson-v-linear-counterexample-targets-2026-09-12.md`
  does not separate it from `P`. It is not a sum of three elements of `V`. It dies at the open questions of
  whether `b_0 ∈ P` and whether `P` is directly finite.
- **Small-support search.** Proposition 4.1 excludes everything [DHJ] covers. The next case,
  `(|c|, |b|) = (3, 5)`, has `|e_h b| <= 15`, so it needs rank pairs `(3, 13)` and `(3, 15)`, which are outside
  [DHJ]. No search was run. Supports range over an infinite set of elements of `V` of unbounded code length,
  and a truncation by code length gives no completeness statement.
- **Trace and Hattori–Stallings.** In characteristic two the identity-coefficient trace has no positivity, and
  `τ(e_h) = 1 = τ(1)`.
- **Eigen-idempotents over `F_4`.** Over `F_4`, `e_h = 1 + ε_ω + ε_(ω²)`, with `ε_λ` the eigen-idempotents of
  `⟨h⟩`. Changing the field gives nothing new, since fullness over `F_2` and over `F_4` are equivalent.
  - One direction is scalar extension.
  - For the other, a solution over `F_4[V]` forces `φ(h) = 1` for every unital `φ` into a directly finite
    `F_4`-algebra, by the argument of Theorem W_V (a) => (c_DF).
  - If `W` is weakly finite of characteristic two, `W ⊗_(F_2) F_4` embeds unitally in the weakly finite ring
    `M_2(W)`. So a representation `ρ : V -> W^x` extends into it and has `ρ(h) = 1`. Hence (d), and (a) over
    `F_2`.

  This remark is on paper here and not in the artifact.
- **Artinian hosts.** A left Artinian ring has a nilpotent radical and a semisimple quotient that is a
  finite product of matrix rings over division rings. So its nilpotents have bounded index, and it is
  excluded by Corollary 3.4. Noetherian hosts in general were not analysed.
- **Characteristic zero.** Kaplansky's positivity makes `C[V]` stably finite, but that transfers nothing to
  characteristic two.
- **Compactness of the equation.** A solution uses finitely many group elements, so it lives in
  `F_2[H]` for a finitely generated `H`. This is subsumed by the target's recorded structural filter and gives
  no new constraint.

## Weakest steps (for a referee)

- The scope transfer of Theorem B of [CS] and Lemma W.2 of [WF] from `R^x` to the host `V`. Both proofs use
  only `g`, `D`, the `π_M` and the block idempotents `f_K`, and [CS] states the scope sentence explicitly. But
  the ESTABLISHED claims are stated for `R^x`.
- Proposition 4.1 rests on the computer enumeration of [DHJ] Proposition 4.21, taken at statement level and
  not re-run.

## Literature consulted (2026-09-16)

- arXiv:1112.1790v4, K. Dykema, T. Heister, K. Juschenko, *Finitely presented groups related to Kaplansky's
  Direct Finiteness Conjecture*. Proposition 4.21 and Remark 4.13 were read in the ar5iv HTML. The
  enumeration was not re-run.
- arXiv API queries on 2026-09-16:
  - "Thompson AND sofic";
  - "direct finiteness AND Kaplansky";
  - title "direct finiteness";
  - "linear sofic";
  - "stably finite AND group algebra";
  - "weakly finite AND Leavitt" (no hits).
- Titles seen in the listings but not read, none about `V` or group algebras of `V`:
  - arXiv:2111.07930, X. K. Phung, *A geometric generalization of Kaplansky's direct finiteness conjecture*;
  - arXiv:2408.16437, *Direct finiteness of representable regular rings with involution: A counterexample*;
  - arXiv:2602.05039, *Linear sofic representations of amenable algebras*;
  - arXiv:2601.18742, *Sofic actions, halo products, and metric approximations of groups*;
  - arXiv:2410.17688, *Strongly sofic monoids, sofic topological entropy, and surjunctivity*.
- Gate result: no 2024–2026 listing found that settles soficity or linear soficity of `V`, direct finiteness of
  `F_2[V]`, or fullness of a finite-subgroup averaging idempotent in a group algebra of `V`. The gate is only as
  good as these keyword queries.

## Referee (2026-09-16)

Adversarial referee and landing agent for this lane.

**What was checked.**
- Read every listed file in full, and the nodes and artifacts they use: the target, [CS]
  (`binary-cyclic-corner-complement-states-2026-09-12.md`, Lemmas 1.1–1.3, Theorem B and its scope sentence), [WF]
  (`binary-weakly-finite-representations-2026-09-12.md`, Lemmas W.1, W.2, Theorem W), [GK3] Section 4, [TGT]
  Sections 2–3, and the claims `binary-cyclic-corner-full-iff-complement-corner-has-no-state` (whose node itself
  records the scope for `D`-stable subgroups containing `g` and the `π_M`),
  `binary-corner-weakly-finite-images-are-unit-representations`, `rank-condition-rings-have-weakly-finite-images`,
  `sylvester-rank-function-quotients-are-weakly-finite`, `finite-subgroups-of-thompson-v-permute-a-canonical-partition`,
  `thompson-v-finitely-presented-infinite-simple`, `leavitt-cylinder-swaps-generate-thompson-in-el`,
  `leavitt-unit-hosts-need-nilpotents-of-unbounded-index`.
- **Lemma 1.1.** Re-traced `k h k^(-1) = g` by hand under the right-to-left convention; it matches. `D(V) ⊆ V` and
  `π_M ∈ V` hold. Re-ran the script: C1–C5 pass.
- **Scope transfer (the flagged weakest step).** Went through Theorem B's proof step by step at `A = F_2[V]`: Lemma
  1.1 (`D(x)` commutes with `g`), Lemma 1.2 (only `C_3^k`, `D` and all `π_M`, which lie in `V`), 4 => 5 (the
  equivalences `x = π_M f_K`, `y = f_K π_M^(-1)` with `M` fixing `K_1`), 5 <=> 6 (a general unital-ring fact) and
  6 => 2. Each ingredient lies in `F_2[V]`. Lemma W.2 likewise uses only `ψ'`, `F_2[A_9]` block identities and `π_M`.
  The transfer is sound.
- **Theorem W_V.** Every implication re-derived. The zero ring is harmless. Remark 2.1 (weakly finite versus directly
  finite) is a genuine consequence of the cycle, not a formal fact; the claim text now says so.
- **Corollary 3.1.** Checked that `θ(y) ∈ V` (refine a code pair until all codes have length at least 2), that `θ` is
  a homomorphism, and that `θ(h) = x`, using that fixed pieces of the canonical partition are fixed by the identity
  replacement.
- **Corollaries 3.2–3.4.** The ascent formula `S[10]T[0] + S[11]T[10] + S[0]T[11] = s_2 t_1 + s_3 t_2 + s_1 t_3`
  matches the target's `t_2 = t0 t1`. The rank ultraproduct is the null quotient of an ultralimit rank function. The
  division-ring and bounded-index arguments are correct (Frobenius on `ρ(x) - 1` in characteristic two).
- **Proposition 4.1.** Fetched arXiv:1112.1790 (v4, 28 Aug 2012) and the ar5iv HTML on 2026-09-16. Definition 4.12
  ("for all groups G and all a,b∈K[G] with rank of a equal to m and rank of b equal to n, ab=1 implies ba=1", rank =
  support size), Remark 4.13 and Proposition 4.21 match the quotations. The deductions are correct. The (3, |b|)
  case is covered directly by 4.21(a), which is symmetric in `min`/`max`, so Remark 4.13 is not even needed. Item 3
  could say `|e_h b| ∉ {1, 3, 5}`; the stated `!= 5` is true and weaker. The enumeration was not re-run, and the
  artifact says so.
- **Notes-only remarks.** The `F_4` equivalence (`W ⊗ F_4 ⊆ M_2(W)`) and the Artinian remark are correct.
- **Citations and gate.** Spot-checked arXiv:2602.05039 (Bachner, *Linear sofic representations of amenable
  algebras*, Feb 2026) and arXiv:2601.18742 (Alekseev–Bradford, *Sofic actions, halo products, and metric
  approximations of groups*, Jan 2026): both exist with the listed titles. An arXiv API query "Thompson AND sofic"
  (2026-09-16) found nothing settling soficity of `V` or finiteness of `F_2[V]`.
- **Discipline.** `bin/cairn search --similar` on the new claim finds no duplicate; `distinct_from` covers the
  nearest nodes. Id lengths are within budget (claim 55 chars). The new hole has `## Attempts`. No `requires: []`
  route was added. The refutation links (`thompson-v-is-f2-linear-sofic`, stable finiteness of `F_p[V]`) are valid.

**What was changed.**
- Route `thompson-v-averaging-fullness-from-no-weakly-finite-rep`: added `leavitt-cylinder-swaps-generate-thompson-in-el`
  to `requires:`, since Theorem B's scope is for subgroups of `L_(F_2)(1,2)^x` and the route needs `V` to be one; a
  sentence records this.
- Claim `thompson-v-has-no-weakly-finite-char-two-representation`: stated that the weakly/directly finite equivalence
  runs through the target and Theorem B.

**Verdict.** Landed with small fixes. The work is a sound, honestly labelled reduction: the order-three target is
equivalent to the OPEN claim that `V` has no nontrivial homomorphism into the units of a weakly (equivalently,
directly) finite ring of characteristic two, with sound consequences and a support filter resting on the verified
statement of DHJ Proposition 4.21. Nothing is solved, and no status is overclaimed.
