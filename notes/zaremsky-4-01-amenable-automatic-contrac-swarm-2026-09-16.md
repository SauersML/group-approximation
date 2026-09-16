# Zaremsky 4.1 via contracting combings: swarm attack, 2026-09-16

- **Lane:** `swarm-zaremsky-4-01-amenable-automat`.
- **Root:** `zaremsky-4-01-amenable-automatic-contractible-rips`.
- **Hole locked and worked:** `amenable-automatic-groups-admit-contracting-combings`.
- **Full proofs:** `research/artifacts/zaremsky-4-01-contracting-combings-2026-09-16.md`.
- **Script:** `experiments/zaremsky-4-01-contracting-combings-2026-09-16/check_combings.py`.

## Setup

The hole says that every amenable automatic group has a finite generating set with a
contracting combing in Alonso's sense. With Alonso's theorem
(`contracting-combings-give-contractible-rips-complexes`) that answers Problem 4.1
positively.

The earlier Attempts said:
- linear fellow-travelling does not give the contracting condition;
- no contracting combing was recorded for any virtually abelian group.

## Status gate (checked 2026-09-16)

- **Zaremsky, "Some open problems".** The PDF is dated July 12, 2026, and was fetched
  and read 2026-09-16. Section 4, Problem 1 is unchanged: "If a group is amenable and
  automatic, does it have a contractible Rips complex? (This would show that F cannot
  be both amenable and automatic.)" Problem 4.3 is marked solved (Virk,
  arXiv:2405.09134). Problem 4.5, on RAAGs with standard generators, has no answer
  marked.
- **arXiv API searches over https**, 2026-09-16:
  - Searches for "contracting combing": no hits.
  - `abs:"contractible Rips"`: 0 hits.
  - Broader Rips/contractible searches found three recent papers. None treats amenable
    or automatic groups, or contracting combings.
- **The three recent papers:**
  - Hulbert–Zaremsky, *Word length, Morse theory, and Vietoris–Rips complexes*,
    arXiv:2608.25614v1 (read): `VR_2(A_Γ)` is contractible for triangle-free `Γ`.
  - Li–Sánchez Saldaña, *Contractible Rips complexes of groups via metric gluings*,
    arXiv:2608.24279v1 (read): type R is closed under graphs of groups with finite edge
    groups; 2-dimensional RAAGs with standard generators are type R; so is
    `Z^n × F`.
  - Gupta–Sarkar–Shukla, arXiv:2511.04238v1: only the arXiv listing was seen, and it
    is off-axis.
- **Conclusion:** Problem 4.1 is open as of 2026-09-16.

## What was established

1. **The recorded definition was wrong, and the wrong reading is degenerate.**
   - The claim `contracting-combings-give-contractible-rips-complexes` recorded the
     contracting condition with `n <= n'`. That came from a ghostscript extraction
     that dropped primes, dated 2026-09-13.
   - A pypdf extraction of arXiv:1812.10976v3 on 2026-09-16 reads "with n′ ≤ n and
     ⌊C/2⌋ ≤ n".
   - Artifact Proposition 1: under `n <= n'` every group satisfying it has
     `|g| <= C + ⌊C/2⌋ − 1`, so it is finite. The hole would then have been false
     (`Z` is a counterexample), and Alonso's theorem vacuous.
   - Both the claim and its citation route are corrected. With `n' <= n`, the condition
     is exactly what the "push the top vertex back" contraction of `VR_t` needs, so the
     citation is sensible.
2. **Positive, `linf-lattice-groups-admit-contracting-combings`** (route `-proof`,
   `requires: []`).
   - *Statement.* Let `G` act transitively on `Z^n` by `v ↦ A_g v + t_g`, with
     `A_g ∈ B_n` and finite stabilizers. For `S = {g ≠ 1 : ‖t_g‖_∞ <= 1}`, the metric
     is `max(‖t_g − t_h‖_∞, 1)`. The clamp combing `t_{s(g)(m)} = κ_m(t_g)` is geodesic
     and contracting for every `C >= 2`.
   - *Key lemma.* The one-dimensional clamp inequality.
   - *Examples.* `Z^n` (l-infinity generators), `Z^n ⋊ F` with `F → B_n`, the Klein
     bottle group, and the scaled `4_1` screw group.
3. **Obstruction, `l1-product-word-metrics-admit-no-contracting-combing`** (route
   `-proof`, `requires: []`).
   - *Statement.* For infinite `G` and `H` with the union of factor generating sets, no
     combing of `G × H` is contracting.
   - *Arrival rule.* If `x ≠ 1`, `d(x, q) <= C` and `d(p'(x), q) > C`, then
     `T(q) >= T(x) + ⌊C/2⌋`.
   - *Square argument.* A square of `C`-moves in alternating factors forces
     `T(x_0) >= T(x_0) + 4⌊C/2⌋`.
   - *Corollaries.* `Z^d` (`d >= 2`) with standard generators and join RAAGs (e.g.
     `F_2 × F_2`) with standard generators have no contracting combing. Existence
     depends on the generating set.
4. **Consequence: Rips contractibility is strictly weaker than having a contracting
   combing for a fixed generating set.**
   - `Z^2` and `F_2 × F_2` with standard generators are type R, by Virk
     (`rips-complexes-of-integer-lattices-are-contractible`) and by Li–Sánchez Saldaña
     (2-dimensional RAAGs).
   - Yet they have no contracting combing.
   - So Alonso's theorem with standard generators cannot give Problem 4.5 for join
     RAAGs. This does not decide Problem 4.5.

## Approaches and where they die

- **Improve the combing of a given automatic structure.**
  - *Dies:* by the obstruction. `Z^2` is automatic over `{±e_1, ±e_2}`, and no combing
    over that set is contracting.
  - *Consequence:* any proof must change the generating set, as the l-infinity set
    does for `Z^n`.
- **Geodesic combings of `Z^d` with standard generators, local analysis.**
  - *Precursor, script Part 3:* the interior backward-vector constraint leaves no
    survivors for `d = 3, 4`, and only `(c/2, c/2)` for `d = 2` with `c` even.
  - *Superseded:* Theorem 5 removes both the geodesic assumption and the `d = 2`
    loophole.
- **Structure route (amenable + automatic ⟹ virtually abelian).**
  - *Would give:* this hole only for the virtually abelian groups covered by the
    positive claim, and Problem 4.1 outright via the existing route
    `amenable-automatic-rips-via-virtually-abelian`.
  - *Dies:* no rigidity theorem of this kind was found. The claim
    `amenable-automatic-groups-are-virtually-abelian` stays open. It would already
    show that Thompson's `F` is not both amenable and automatic (route
    `thompson-f-not-both-via-amenable-automatic-virtually-abelian`), which indicates
    how strong it is.
- **Remaining virtually abelian cases, such as `p3` and `p6`.**
  - *Gap:* a properly acting group transitive on `Z^m` is quasi-isometric to `Z^m`, so
    `p3` would need `m = 2`. `B_2` has no element of order 3, and `p3` is generated
    by rotations of order 3, so `p3` would act by translations with finite kernel,
    which is impossible. So the positive claim cannot cover any plane group containing `p3`,
    in any coordinates. In dimension 3 some trigonal groups are covered, for example
    `Z^3 ⋊ C_3` with cyclic coordinate permutation (referee correction).
  - *Candidate:* a hexagonal-norm clamp (clamping in the three directions of the
    triangular lattice) is the natural next attempt. It was not tried.
  - *Status:* no construction and no obstruction is known.
- **Amenability as a mechanism.**
  - *Dies:* no mechanism was found that turns Følner sets or amenability into the
    backward-step control the contracting condition needs. The contracting condition
    is a one-sided "stepping back keeps close neighbours close" property.
  - *Contrast:* for trees it holds automatically; flat `l^1` directions break it, as
    Theorem 5 shows.

## Experiments

`experiments/zaremsky-4-01-contracting-combings-2026-09-16/check_combings.py`,
single-threaded, about 45 s, exit 0. It is evidence, not proof.

| Part | What it checks | Result |
| --- | --- | --- |
| 1 | The clamp inequality | 762300 cases, 0 failures |
| 2 | Theorem 3 on five groups | Metric formula and contracting condition for `C = 2..5`, 0 failures |
| 3 | Local precursor analysis | As above |
| 4 | One geodesic combing of `Z^2` std | Fails for `C = 4, 5` |
| 5 | Square certificate generator | Violations found for four combings of `Z^2` std, every `C` in `2..7` |

## Literature consulted

- M. C. B. Zaremsky, *Bestvina–Brady discrete Morse theory and Vietoris–Rips
  complexes*, arXiv:1812.10976v3 (v3 dated 28 March 2021). Section 6.1 and Citation
  6.7 were read 2026-09-16 via pypdf extraction.
- M. C. B. Zaremsky, *Some open problems*, PDF dated July 12, 2026. Section 4 was read
  2026-09-16.
- S. Hulbert, M. C. B. Zaremsky, *Word length, Morse theory, and Vietoris–Rips
  complexes*, arXiv:2608.25614v1. Abstract and introduction read 2026-09-16.
- K. Li, L. J. Sánchez Saldaña, *Contractible Rips complexes of groups via metric
  gluings*, arXiv:2608.24279v1. Abstract and introduction read 2026-09-16.
- arXiv:2511.04238v1 (Gupta–Sarkar–Shukla). Only the API listing was seen, 2026-09-16.
  It is off-axis.
- Ž. Virk, arXiv:2405.09134. Cited through Zaremsky's list and the existing node; not
  re-read.
- J. M. Alonso, *Combings of groups*, in *Algorithms and Classification in
  Combinatorial Group Theory*, MSRI Publ. 23 (1992). Unverified: the fetch failed
  (404, connection reset). Everything here concerns the definition as transcribed by
  Zaremsky.

## Referee (2026-09-16)

**Checked.**
- *Source text.* I downloaded arXiv:1812.10976v3 again and extracted it with pypdf.
  Section 6.1 reads verbatim "with n′ ≤ n and ⌊C/2⌋ ≤ n, if d(s(g)(n), s(h)(n′)) ≤ C
  then also d(s(g)(n − ⌊C/2⌋), s(h)(n′)) ≤ C". So the correction of
  `contracting-combings-give-contractible-rips-complexes` and its citation route is
  right and essential.
- *Sanity check of the corrected reading.* Geodesic combings of free groups satisfy
  it: in a tree, stepping back either shortens the distance or leaves it at most `c`.
  So the definition is not degenerate.
- *Problem status.* I fetched Zaremsky's *Some open problems* (PDF dated July 12,
  2026). Section 4, Problem 1 is unchanged, so Problem 4.1 is open. The arXiv abstract
  of 2608.25614 (Hulbert–Zaremsky) matches the note.
- *Proofs.* I re-derived each of these line by line:
  - Proposition 1 (the reversed reading forces finiteness);
  - Lemma 2 (all cases);
  - Theorem 3(a) (lower and upper bounds for the word length, the metric formula) and
    3(b);
  - Lemma 4 (the arrival rule, used with `n = n'`, which the condition allows);
  - Theorem 5, Claims 1 and 2 and the square. Both factors are infinite, so `g'`,
    `h'` exist and all four corners are nontrivial.

  I found no gap. Both `requires: []` routes are complete for the definition as
  Zaremsky states it.
- *Examples.* I checked the Klein bottle and screw-group actions by composing the
  maps.
- *Computation.* I ran `check_combings.py` (exit 0, about 74 s). I also wrote an
  independent check, `referee_r3_check.py`, for `Z^3 ⋊ C_3` with cyclic coordinate
  permutation. It confirms the BFS metric formula on the ball of radius 4 and finds 0
  contracting failures in 5625000 checks for `C = 2, 3, 4`.

**Changed.**
- The scope statement "`p3`, `p6` and the other trigonal and hexagonal groups are not
  covered" was too broad. In dimension 3, `Z^3 ⋊ C_3` with cyclic coordinate
  permutation, which is rhombohedral trigonal, is covered by example (ii).
- The argument that `p3` is not covered ("`B_2` has no element of order 3") was
  incomplete. I added the missing steps: `p3` is generated by its rotations of order 3,
  so it would act by translations, and its infinite commutator subgroup would fix `0`.
  With them, every plane group containing `p3` is excluded (for
  groups such as `p3 × Z` in dimension 3 it is not settled).
- Where the fix went: the claim `linf-lattice-groups-admit-contracting-combings`, the
  artifact (Section 3 scope and Section 6 item 2), the hole's Attempts entry, and this
  note.

**Boundaries.**
- Alonso's original paper is still unread. Everything is relative to Zaremsky's
  transcription, which I verified.
- Novelty of Theorems 3 and 5 is not audited beyond the solver's arXiv API searches.
  My web search budget was exhausted, and the results may be known to experts. The
  nodes do not claim novelty.

**Verdict.** Sound. Landed with the scope fixes above.
