# Zaremsky 2.15 (reposed): bi-orderable subgroups of V without free subgroups — swarm lane, 2026-09-16

Target root: `zaremsky-2-15b-bi-orderable-subgroups-of-v-embed-in-f`. Does every
bi-orderable subgroup of `V` with no non-abelian free subgroup embed in `F`?

- Lock held: `wreath-z-by-z2-embeds-in-thompson-v`.
- A second lock attempt on `infinite-order-elements-of-v-have-hyperbolic-periodic-points`
  returned exit 3: another agent took it at 01:12 UTC. So its proof below went into an
  artifact, not a route.

## 1. Problem status (checked 2026-09-16)

- Zaremsky's open-problems list (PDF version of July 12, 2026, fetched 2026-09-16): the
  reposed Problem 2.15 is still listed as open.
- Nothing in the 2024–2026 arXiv listings searched (API queries on Thompson `V`,
  bi-orderable, embeddings, co-context-free, irrational slope) answers it.
- Hyde–Skipper–Zaremsky, arXiv:2605.20564v2 (TeX source): `F_{2,3}` and the multi-slope
  Stein groups do not embed in `V`. Their closing remark says they cannot rule out `F_τ`
  and do not know about `F_{3/2}`.
- Bodart–D'Angeli–Perego–Rodaro, arXiv:2608.02111 (abstract): characterises finitely
  generated subgroups of `V` by faithful context-free actions. No bi-orderable examples.

## 2. Status update on the locked hole: Z ≀ Z^2 is NOT a subgroup of V

- **Corwin**, PhD thesis, UNL 2013, https://digitalcommons.unl.edu/mathstudent/48. The
  landing page and abstract were fetched 2026-09-16. It proves the "nonexistence of the
  wreath product Z wr Z^2 as a subgroup of V, proving a conjecture of Bleak and
  Salazar-Diaz". The PDF returned 403 (Cloudflare), so the proof was not read.
- **Burillo–Cleary–Röver**, *Obstructions for subgroups of Thompson's group V*,
  arXiv:1402.3860v2. The TeX was fetched 2026-09-16. It restates the result as a theorem
  citing Bleak–Salazar-Díaz (TAMS 365 (2013)) and Corwin: "Neither the free product
  $\Z*\Z^2$ nor the standard restricted wreath product $\Z\wr\Z^2$ ... are subgroups of
  $V$."

Graph changes:
- New claim `wreath-z-by-z2-does-not-embed-in-thompson-v`, with citation route
  `wreath-z-by-z2-does-not-embed-in-thompson-v-citation`.
- `refuted_by` added to `wreath-z-by-z2-embeds-in-thompson-v`, plus an Attempts bullet.
  Once the import is accepted, route `biorderable-v-subgroup-not-in-f-via-wreath-z-by-z2`
  is invalidated automatically.

So the 2026-09-13 lane's search for a `Z ≀ Z^2` embedding (overlapping lamps) was doomed.
The dead ends it recorded (wandering lamps, two-cone models) are consistent with Corwin's
dynamical proof.

## 3. Proven this session: V0 (infinite-order elements of V have hyperbolic periodic points)

Full proof: `research/artifacts/infinite-order-v-elements-hyperbolic-points-2026-09-16.md`.

Setup. Take `g` in `V` with pieces `u_i ↦ v_i`. Put `N = max(|u_i|, |v_i|)` and
`D = max ||u_i| − |v_i||`. The length cocycle is `λ(x) = |u| − |g_*(u)|` on any prefix
`u` of `x` on which `g` is a prefix replacement. Put `S_k(x) = Σ_{i<k} λ(g^i x)`.

- *Lemma 1.* If `S` is bounded by `K`, then every `g^k` is a prefix replacement on all
  words of length `N + K`, with images of length in `[N, N + 2K]`. There are finitely many
  such maps, so `g` has finite order.
- *Lemma 2.* Suppose `S_k(x) > D(2^N − 1)`. The strict record times of `m ↦ S_m(x)` raise
  the maximum by at most `D` each, so there are at least `2^N + 1` of them, and two
  records `m < m'` share the `N`-prefix `w`. Pull the cone `w` back from `x_{m'}` to
  `x_m`. Every intermediate cone has length `N + s_{m'} − s_{m''} ≥ N`, because `m'` is a
  record. So `g^{m'−m}` maps `w r y ↦ w y` with `|r| = s_{m'} − s_m ≥ 1`, and `w r^∞` is
  a hyperbolic periodic point.
- *Theorem.* If `g` has infinite order, Lemma 1 gives unbounded `S`. Lemma 2 then applies
  to `g`, or to `g^{-1}` using `S^{g^{-1}}_k(g^k x) = −S_k(x)`.

This fills exactly the two gaps named in the claim's 2026-09-13 Attempts ("lengths grow
without nesting" and "global finite order"). The route into
`infinite-order-elements-of-v-have-hyperbolic-periodic-points` was NOT written because
another agent holds that lock. Whoever lands that hole can cite the artifact in a
`requires: []` route.

Once V0 is established, routes `v-excludes-bs-1-n-from-hyperbolic-points` and
`v-nilpotent-abelian-from-hyperbolic-points` become complete. Secondhand, the statement
also matches Higman's theorem quoted in BCR: some power of an infinite-order `v` has a
source leaf paired with its own child.

Sanity check (evidence only): `experiments/zaremsky-2-15b-v0-2026-09-16/check_v0.py`.
- It draws random elements of `V` with 2–5 pieces and starts from near a repeller.
- Whenever the drift exceeds `D(2^N − 1)`, it checks the record count `≥ 2^N + 1`, the
  pull-back lengths and the relation `g^{m'−m}(w r y) = w y`.
- Seeds 1, 2 and 3 gave 920 Lemma 2 cases, all verified, with 0 failures (`output.txt`).

## 4. Surviving candidates for the negative answer

With `Z ≀ Z^2` gone, the natural witnesses are non-`F` subgroups of `PL_+(I)` whose germ
groups are cyclic. These are exactly the groups the HSZ methods cannot touch:

- **Cleary's `F_τ = F([0,1]; Z[τ], ⟨τ⟩)`.** It is not a subgroup of `F` (Hyde–Moore,
  GGD 17 (2023), Cor. 1, arXiv:2103.14911). HSZ say they cannot rule it out of `V` but
  expect it is not in `V`.
- **`F_{3/2}` (= `F_{2/3}`).** It is not a subgroup of `F` (Belk–Hyde–Moore,
  arXiv:2211.05825, abstract, combined with Hyde–Moore). It is finitely generated
  (Burillo–Felipe, arXiv:2409.09195). HSZ do not know whether it embeds in `V`.

Both are bi-orderable (germ order at the leftmost moved point) and free-subgroup-free
(Brin–Squier).

Graph changes:
- New claim `cleary-golden-ratio-group-does-not-embed-in-thompson-f`, with citation route
  `cleary-golden-ratio-group-not-in-f-citation`.
- New open hole `cleary-golden-ratio-group-embeds-in-thompson-v`, with Attempts.
- New route `biorderable-v-subgroup-not-in-f-via-golden-ratio-group`, which requires both
  and targets `biorderable-subgroup-of-v-without-free-subgroups-not-in-f`.
- `F_{3/2}` is recorded as a sibling candidate in the hole's Attempts. It has no node of
  its own.

## 5. Obstructions tested against F_τ and F_{3/2}, and where each dies

1. *Distorted cyclic subgroups* (BCR: cyclic subgroups of `V` are undistorted). This
   dies: every cyclic subgroup of a finitely generated subgroup of `PL_+(I)` is
   undistorted. With `σ(w) = max |log w'(x+)|`, `σ` is subadditive, and `σ(g^n) ≥ n·|log λ|`
   at a bump endpoint. Short proof in the hole's Attempts. (BCR has a commented-out
   remark claiming distortion in `F(2,3)`. This argument shows it cannot hold. The reason
   the remark was commented out is not known.)
2. *Corwin / Bleak–Salazar-Díaz* (`Z ≀ Z^2`, `Z * Z^2`). These die: neither group is a
   subgroup of `F_τ` or `F_{3/2}`. For `Z ≀ Z^2`, part 2 Theorem N4 covers any cyclic
   slope group. For `Z * Z^2`, Brin–Squier applies.
3. *Germ obstructions from V0* (`BS(1,n)`, non-abelian nilpotent groups). These die: such
   groups are already excluded from `PL_+(I)` (part 1, N1 and N2).
4. *HSZ semiconjugacy rigidity.* It needs a non-cyclic germ group. This dies, as the
   authors say.
5. *Open, not attempted.*
   - Is the co-word problem of `F_τ` context-free? `V` is co-context-free by
     Lehnert–Schweitzer, not re-read.
   - Does `F_τ` have a faithful context-free action (BDPR)?
6. *Heuristic.* Recoding `F_τ`'s two-caret subdivision tree as `{0,1}^ω` with a fixed
   splitting seems to need golden-base carries, i.e. transducers with memory rather than
   prefix replacements. This is not checked.

## 6. The positive direction

Nothing new. `biorderable-subgroups-of-v-without-free-subgroups-embed-in-f` stays open.
Any proof must in particular exclude `F_τ` and `F_{3/2}` from `V`, which HSZ could not do.
So the positive direction is at least as hard as those two named open questions.

## 7. Literature consulted (dates are fetch dates)

- N. Corwin, PhD thesis, UNL 2013: landing page and abstract (2026-09-16). PDF 403.
- J. Burillo, S. Cleary, C. E. Röver, arXiv:1402.3860v2: TeX source (2026-09-16).
- C. Bleak, O. Salazar-Díaz, TAMS 365 (2013) 5967–5997, arXiv:0911.0979: cited via BCR
  and the abstract (2026-09-16).
- J. Hyde, R. Skipper, M. C. B. Zaremsky, arXiv:2605.20564v2: TeX source (2026-09-16).
- J. Hyde, J. T. Moore, arXiv:2103.14911 (GGD 17 (2023)): abstract (2026-09-16).
- J. Belk, J. Hyde, J. T. Moore, arXiv:2211.05825v4: abstract (2026-09-16).
- J. Burillo, M. Felipe, arXiv:2409.09195: cited via HSZ bibliography. The referee checked the
  arXiv API abstract on 2026-09-16: it gives a two-element generating set for `F(3/2)`.
- C. Bodart, D. D'Angeli, E. Perego, E. Rodaro, arXiv:2608.02111: abstract.
- arXiv:2608.16530, arXiv:2608.01168, arXiv:1107.0672: abstracts, checked for relevance
  (2026-09-16).
- M. C. B. Zaremsky, open problems list, PDF version of July 12, 2026 (fetched
  2026-09-16).
- Brin–Squier (Invent. Math. 79 (1985)) and Lehnert–Schweitzer (Bull. LMS 2007): cited as
  standard, not re-read.

## Referee (2026-09-16)

### What was checked

- **Corwin import** (`wreath-z-by-z2-does-not-embed-in-thompson-v` and its citation route).
  - The UNL abstract quote and the BCR theorem statement (arXiv:1402.3860v2 TeX) were
    re-fetched. Both match verbatim.
  - The trust boundary (thesis PDF 403, proof unread) is honest.
  - The `refuted_by` edit to the committed node `wreath-z-by-z2-embeds-in-thompson-v` is the
    proper refutation mechanism. It does not rewrite the hole's history.
  - `bin/cairn context` shows the hole REFUTED and route
    `biorderable-v-subgroup-not-in-f-via-wreath-z-by-z2` INVALIDATED.
- **Hyde–Moore import** (`cleary-golden-ratio-group-not-in-f-citation`).
  - The arXiv TeX of 2103.14911 was fetched. The first corollary (`\label{Ftau}`) is exactly
    "Cleary's group $F_\tau$ does not embed into $F$". So "Corollary 1" is correct.
  - Crossref confirms GGD 17(2) 533–554, DOI 10.4171/ggd/708.
  - The HSZ closing-remark quote was verified verbatim.
  - The τ versus 1/τ convention is harmless: same ring, same cyclic group.
- **Route `biorderable-v-subgroup-not-in-f-via-golden-ratio-group`.**
  - The bi-orderability argument (step 2: right slope at the leftmost moved point gives a
    conjugation-invariant positive cone) was re-derived and is correct.
- **Hole `cleary-golden-ratio-group-embeds-in-thompson-v`.**
  - The Attempts are accurate.
  - The undistortedness argument in `PL_+(I)` is correct.
  - Part 2 Theorem N4 does cover cyclic slope groups.
- **V0 artifact.** Read line by line.
  - Lemma 1: bounded cocycle ⇒ finitely many prefix-replacement maps ⇒ finite order.
  - Lemma 2: the record-time pigeonhole, the pull-back lengths staying `≥ N` because `m'`
    is a record, and the resulting `w r y ↦ w y`.
  - The Theorem's inversion identity.
  - All sound.
  - `check_v0.py` was re-run with seed 1 and reproduced 345/345.
  - Not routed, correctly: another agent holds the lock on the V0 claim.
- **Duplicates.** `bin/cairn search --similar` on the new ids found only the intended
  F-versus-V pairs, which are resolved by `distinct_from`.

### What changed

- **Gap fixed.** Step 3 of the golden-ratio route ("`H` has no non-abelian free
  subgroup") relied on Brin–Squier for `F_τ`. The only free-subgroup import in the graph is
  `thompson-f-no-free-subgroups-citation`, which covers `F`, not `PL_+([0,1])`, and the route
  did not list any prerequisite for it.
  - Added claim `pl-plus-interval-has-no-non-abelian-free-subgroups`, with citation route
    `pl-plus-interval-no-free-subgroups-citation`. It imports Monod, PNAS 110 (2013),
    arXiv:1209.5229, from the TeX: "The group $H$ does not contain any non-abelian free
    subgroup". It also records the explicit embedding `PL_+([0,1]) ↪ H`, and Brin–Squier by
    bibliographic record only.
  - The route now requires that claim.
- The Hyde–Moore route's trust boundary now records the referee's TeX and Crossref checks.
- The hole's Attempts cite the claim ids for N1 and N2 instead of "part 1".
- Notes §5 item 1: removed the speculation about why BCR commented out a remark.
- Notes §7: Burillo–Felipe is now checked from its abstract.

### What is established after refereeing

- `Z ≀ Z^2` is not a subgroup of `V` (import). So the `Z ≀ Z^2` route to a negative answer
  is dead.
- `F_τ` is not a subgroup of `F` (import).
- *If* `F_τ` embeds in `V`, the root has answer NO. This implication is complete given its
  prerequisites.
- V0 has a verified direct proof in an artifact, pending a route by the lock holder.
- Open, and unchanged: whether `F_τ` (or `F_{3/2}`) embeds in `V`, and the positive
  direction.

### Verdict

Landed with fixes.
