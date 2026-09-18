# BS(1,3) ≤ 3V: write-up skeleton

Compiled by lane `gq-writeup` from the Cairn nodes on origin/main at `89063a2ee` (2026-09-18 01:24 local).
It is a skeleton for a write-up and makes **no claim beyond the nodes it cites**. The proof sketches
compress the recorded proofs, and the detailed arguments are in the artifacts those nodes name.

Commits:
- `d4064ce79`: BS(1,3) ≤ 3V established;
- `eddfd3d4b`: exact tripling;
- `be2fe0964`: odometer factor;
- `9fadf5ac6`: the renormalization claimed;
- `81066618e`: the criterion;
- `4eb6fec15`: the odd-branching lemma.

## 0. Setting and wording

- **Brin–Thompson groups.** `kV` acts on `C^k` by brick-wise prefix replacements (Brin). "Brin–Thompson group"
  below always means Brin's `nV`. It does not mean the twisted groups `SV_G`: Bux–Llosa Isenrich–Wu
  (arXiv:2408.05673) already put Baumslag–Solitar groups in those, through a type (A) actor
  (`research/artifacts/gq-gq-lit-arxiv-priority.md` §10).
- **Known before.**
  - `V` contains no `BS(1,n)` or `Z[1/n]` for `n >= 2` (`bs-1-n-does-not-embed-in-thompson-v`), while
    `BS(m,±m) ≤ V`.
  - Callard–Salo (arXiv:2208.00685v3, Theorem E) give a distortion element of `mV` with `|f^N| = O(log^4 N)`.
    It "roughly corresponds to the SMART machine of Cassaigne, Ollinger, and Torres-Avilés".
- **SMART.** A 4-state, 3-letter reversible Turing machine (Cassaigne–Ollinger–Torres-Avilés), used here through
  Callard–Salo's transcription and `prop:smart-moves`, read from the e-print source `distortion-1-smart.tex`.
  Its moving-tape map `F` is an element of `2V` with no periodic point, by complete prefix codes
  (`three-v-contains-aperiodic-rationals`, item 1).

## 1. Main theorem

**Theorem A** (`bs13-embeds-in-brin-thompson-3v`; route `bs13-in-3v-via-smart-renormalization`). There are
`s, u ∈ 3V` with `s` of infinite order and `u s u^(-1) = s^3`. So `BS(1,3) = ⟨a, t | t a t^(-1) = a^3⟩ ≅ ⟨s, u⟩`
embeds in `3V`. Both inputs of the route were reviewed PASS: gq-referee-a (12b5beb4a) and gq-referee-b
(b6d33ae8e).

**What the node records as consequences, with its wording caveats.**
- **Priority.** On a bounded search it is the first `BS(1,n)` with `|n| >= 2` known in any Brin–Thompson group
  `nV` (gq-lit-arxiv, e78b09c00; no MathSciNet).
- **Distortion.** `|s^(3^n)| = O(n)` in `3V`: logarithmic along powers of 3, compared with Callard–Salo's
  `O(log^4 N)`. The priority artifact says no element of `nV` with `O(log N)` distortion was known.
- **Not an answer to Callard–Salo.** It does **not** answer their question for `Aut(A^Z)` ("It is not known
  whether the Heisenberg group or the Baumslag-Solitar group BS(1,2) embed in Aut(A^ℤ)"). It does not answer
  Salo's `Aut_2` question, and it says nothing about `BS(1,2)`.
- **Consistency.** It is consistent with the withdrawal of Sheng arXiv:2209.11982 (v2, "a flaw in one of the
  proofs"), whose abstract excluded some Baumslag–Solitar groups from `SV` and `SV_G`.
- **For the GL_n(Q) programme.** The Baumslag–Solitar gate of
  `rational-stepping-stones-in-nv-need-bs12-or-heisenberg` is passable at the prime 3. The gate at the prime 2,
  which `GL_2(Q)` and `Aff(Q)` need, stays open (`bs12-embeds-in-brin-thompson-2v`, OPEN).

## 2. The criterion

**Theorem B** (`renormalizable-thompson-elements-give-baumslag-solitar`; route `-proof`, `requires: []`;
gq-referee-c PASS 894d10d19). Let `T ∈ kV` on `X = C^k`, `m >= 2`. A **height-m renormalization** is a pair
`(A, φ)` with three properties:
1. `A` is clopen, `X = A ⊔ TA ⊔ … ⊔ T^(m-1)A`, and `T^m A = A`;
2. `φ : A → X` is a homeomorphism with `φ ∘ T^m|_A = T ∘ φ`;
3. `φ` is **brick-local**: a finite brick partition of `A` on which `φ` is a prefix replacement.

If `T` has one, then `s = T × id ∈ (k+1)V` and some `u ∈ (k+1)V` satisfy `u s u^(-1) = s^m`, and
`⟨s, u⟩ ≅ BS(1,m)`. Infinite order of `T` is automatic from item 1 and item 2 (remark of gq-referee-c).

*Proof sketch.*
- **The conjugator.** Take a complete prefix code `c_0, …, c_(m-1)` and put `g(T^i a, y) = (φ(a), c_i y)` for
  `a ∈ A`. It is a bijection, and it lies in `(k+1)V`: composites of brick-local prefix replacements are again
  prefix replacements, with `ε ↦ c_i` in the new coordinate.
- **It conjugates.** `g s^m = s g` follows from item 2, so `u = g^(-1)` works.
- **Faithfulness.** The kernel of `BS(1,m) → ⟨s,u⟩` meets `Z[1/m]` trivially, because `s` has infinite order.
  So it embeds in the quotient `Z` and centralizes `Z[1/m]`, which forces it into `Z[1/m]`; hence it is trivial.
- **Model.** The binary odometer with `A = C(0)`, `φ(0w) = w`. There `g` is the baker map, and the construction
  fails only because the odometer is not in `V`.

## 3. The SMART inputs

**Lemma C, exact tripling** (`smart-induced-on-genuine-moves-has-exact-tripling`; route `-proof`; lane
gq-affq; *lane proof, not independently reviewed*). Let `Y` be the clopen set of phase-2 configurations that are
genuine level-0 moves.
- Every configuration enters `Y` within 5 steps, and `r_Y <= 6`.
- So `S = F_Y` is brick-locally conjugate to an element of `2V`, by
  `brin-thompson-first-return-maps-lie-in-kv` (lane proof, not independently reviewed).
- Exactly `3^k` of the `f(k) = 3^(k+1) - 2` steps of each level-`k` move `M_q(k)` start in `Y`. So `e(k) = 3^k`
  and `e(k+1) = 3e(k)` exactly, while `f(k+1) = 3f(k) + 4` in the uninduced map.

**Lemma D, odometer factor** (`smart-level-zero-return-map-factors-onto-3-adic-odometer`; route `-proof`;
gq-referee-a PASS 6000c8af8, gq-referee-b PASS 628a5c79d). Take `Y` to be the configurations performing a step
of a level-0 move. Then `F_Y` has a continuous factor `π = (pos_k)_k : Y → Z/2 × Z_3` with `π ∘ F_Y = π + 1`.
It is conjugate to an element `U ∈ 2V`, so `U` factors onto the 3-adic odometer.

This answers `some-brin-thompson-element-factors-onto-an-odometer` YES, with `k = 2`, `m = 3`, through route
`odometer-factor-via-smart-level-zero-return-map`.

*Mechanism.*
- Moves nest by the constant-length-3 substitution `b→bdp, d→dbq, p→bqp, q→dpq`, with 2 special configurations
  per move.
- The parent of each move is read off two unmodified cells (Callard–Salo, `fig:bottom-up-analysis-smart`).
  So `pos_k` is a locally constant function of `k+2` cells.
- MSI simulation: seven runs of `3^11` steps, with 0 phase conflicts for `k = 1..7`.

Its role: `renormalizable-thompson-elements-are-odometer-codes` makes an odometer factor necessary for the
renormalization route. Lemma D shows SMART passes that test. It does not give the renormalization.

**Lemma E, head-adjacent renormalization** (`smart-induced-map-has-brick-local-height-3-renormalization`;
route `-proof`, requiring Lemma C and `brin-thompson-first-return-maps-lie-in-kv`; lane gq-nv-obstruct).
Referees: gq-referee-a PASS 12b5beb4a, gq-referee-b PASS b6d33ae8e, gq-referee-c PASS 894d10d19.

*Statement.* Let `U = F_Y ∈ 2V` as in Lemma C, and let `A ⊆ Y` be the first `Y`-points of level-1 moves.
Then `Y = A ⊔ UA ⊔ U^2A`, and `φ : A → Y` is a brick-local homeomorphism with `φ ∘ U^3 = U ∘ φ`.

*The four cases of φ.*
- At a start of `M_b(1)`, delete the `0` right of the head.
- At a start of `M_d(1)`, delete the `0` left of the head.
- At the first `Y`-point of `M_p(1)`, delete the head cell, move the head left, and change the state to `p_2`.
- The `M_q(1)` case is the mirror image.

*Proof sketch* (artifact `research/artifacts/gq-gq-nv-obstruct-smart-renormalization.md` §1–§3).
- **Induction on the level K**, using `prop:smart-moves`: at the start of its ρ-th level-1 sub-move, `M_x(K)` is
  `M_x(K-1)` at its ρ-th level-0 sub-move plus one cell in the innermost 3-cell region. The side of the extra
  cell and the junction values `β` do not depend on the level.
- **Dense set.** The identity holds wherever `y` and `U^3 y` share a finite-level move. The remaining points
  lie on all-`p` or all-`q` ancestor chains, which one far-away cell edit breaks. So the good points are
  dense, and continuity finishes.
- **Brick-locality.** Deleting the head's neighbour is the prefix replacement `P(q,c_0) D(c_1) → P(q,c_0)` in
  the moving-tape coding.

*Numerical validation* (gq-affq, MSI, cba5854a6).
- 55,000 whole-tape checks of `φ S^3 = S φ`, at densities `P(0) = 1/3, 0.5, 0.9, 0.97`, with no failure.
- The tower period is exactly 3, and the explicit inverse passes 8,069 checks.
- An earlier negative search was retracted as a harness artefact: its window of 120 was smaller than its
  equality radius of 150.

## 4. Assembly of Theorem A

1. Lemma C: `U ∈ 2V`, SMART induced on genuine level-0 moves.
2. Lemma E: `(A, φ)` is a height-3 renormalization of `U`.
3. Theorem B with `k = 2`, `m = 3`: `s = U × id` and `u ∈ 3V` satisfy `u s u^(-1) = s^3`, so `⟨s,u⟩ ≅ BS(1,3)`.
   Infinite order of `U` is automatic by referee c's remark. The route also cites SMART's aperiodicity.

## 5. Why BS(1,2) is harder

**Lemma F, odd branching** (`crossing-move-hierarchies-have-odd-branching`; route `-proof`, `requires: []`;
lane gq-nv-obstruct; *elementary lane proof, not independently reviewed*).

*Setting.* A one-head moving-tape system has a move hierarchy with bounded junctions `B` and domain growth
`d(k+1) - d(k) <= c`, where `d(k) → ∞`.

*Statement.* For large `k`:
- a level-`(k+1)` crossing has an odd number of sub-crossings;
- a level-`(k+1)` return has an even number;
- so if every move is a crossing, every branching number is odd. SMART's moves are all crossings, and it branches
  by 3.

*Proof sketch.* The end clusters `L` and `R` of a domain are more than `2B` apart. The head moves one cell per
step, so the junctions cannot jump between clusters. Only sub-crossings switch the cluster containing the head.

*Consequence.* A binary hierarchy needs return moves: the Jacobsthal scheme `C→ ↦ C→ R_R`, `R_R ↦ C← C→`. Its
returns turn one cell short of the domain end, and the turn has to be triggered by marks written near the head.
The exhaustive searches in `research/artifacts/gq-gq-nv-obstruct-binary-smart-search.md` found no such machine in
the classes searched, including the full mirror-symmetric one-head binary class with 8+8 states (4,200 machines with at least 10 levels ranked). Every binary counter found had an exact
binary skeleton plus an unbounded linear walk. So the SMART route gives the prime 3, and the prime 2 needs a
machine of a different shape.

## 6. Trust record

| Input | Node | Checks |
|---|---|---|
| Criterion: renormalization gives BS(1,m) | `renormalizable-thompson-elements-give-baumslag-solitar` | referee c PASS; referee b reviewed it in full within Lemma E's review |
| Height-3 renormalization of U | `smart-induced-map-has-brick-local-height-3-renormalization` | referees a, b, c PASS; 55,000 numerical checks |
| Exact tripling; U ∈ 2V | `smart-induced-on-genuine-moves-has-exact-tripling` | lane proof, not independently reviewed; referee a re-derived the first-Y-point table used |
| First-return maps lie in kV | `brin-thompson-first-return-maps-lie-in-kv` | lane proof, not independently reviewed |
| F ∈ 2V by prefix codes; F aperiodic | `three-v-contains-aperiodic-rationals`, item 1 | lane proof, not independently reviewed; aperiodicity is cited from SMART's literature |
| SMART table and `prop:smart-moves` | Callard–Salo arXiv:2208.00685v3 e-print | read verbatim; the transcription was checked reversible |
| Odometer factor (context, not an input) | `smart-level-zero-return-map-factors-onto-3-adic-odometer` | referees a, b PASS |
| Odd branching (context) | `crossing-move-hierarchies-have-odd-branching` | lane proof, not independently reviewed |
| Priority | `gq-gq-lit-arxiv-priority.md` §10 (e78b09c00) | bounded search, no MathSciNet |

## 7. Open points recorded in, or visible from, the nodes

- **Stale prose.**
  - `bs13-embeds-in-brin-thompson-3v` still has a section headed "What it would give", written in the
    conditional, and says "A priority check is requested". The check was done (e78b09c00).
  - `smart-induced-on-genuine-moves-has-exact-tripling` still lists the renormalization under "Not
    established". It is now Lemma E, in its own node.
- **Unreviewed inputs.** Three lane nodes in the chain have no independent review of their own: the tripling
  node, the first-return tool and the prefix-code encoding. Lemma E's referees re-derived the parts they use.
- **Compatibility across primes** (criterion node, last paragraph). `aff-q-embeds-in-fp-simple-group` needs,
  for every prime `p`, an element conjugate to its `p`-th power inside one copy of `Q`. This is not addressed.
- `BS(1,2)` in any `nV` stays OPEN.
- **kV-native designs, not built** (binary-search artifact §3c). An element of `kV` can insert or delete a cell
  next to the head, which a Turing machine cannot. The parity lemma still applies while domains grow by a
  bounded amount per level, so such designs can only move where the domain ends lie.

## 8. What an expert should check

1. The SMART transition table and `prop:smart-moves` against Cassaigne–Ollinger–Torres-Avilés and Callard–Salo.
   The graph read Callard–Salo's e-print source only.
2. Lemma C: that `Y` is clopen, the return bound `r_Y <= 6`, and the count of exactly `3^k` `Y`-starts per
   level-`k` move.
3. The first-return tool: bounded return implies brick-local conjugacy into `kV`.
4. Lemma E, the four-case table of first `Y`-points of level-1 moves, and that `A` is read at radius 1.
5. Lemma E, the induction `φ(C1_K) = C0_(K-1)`: level-independence of the extra-cell side and of `β`.
6. Lemma E, the density step. Failures of `φU^3 = Uφ` are exactly the all-`p` or all-`q` ancestor chains, and
   these are nowhere dense.
7. Brick-locality of `φ` after transport into `2V`. The deletion must be a prefix replacement in the chosen
   coding.
8. Theorem B: that `g` lies in `(k+1)V`, the identity `g s^m = s g`, and faithfulness of `BS(1,m) → ⟨s,u⟩`.
9. Priority: MathSciNet and the reversible-cellular-automaton literature for `BS(1,n)` in `nV`, `RTM(n,k)` or
   `Aut(A^Z)`. Also whether "Brin–Thompson group" in any claim is kept distinct from `SV_G`.
