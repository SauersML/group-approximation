# Thompson's group F automatic (Zaremsky 2.2): swarm attack, 2026-09-16

- **Lane:** `swarm-thompson-f-is-automatic`.
- **Root:** `zaremsky-2-02-thompson-f-automatic`. Its body forbids `requires: []`
  routes into the root; none were written there.
- **Hole locked and worked:** `thompson-f-is-automatic`.
- **Outcome:** obstruction. The hole stays open. Two candidate languages that
  earlier Attempts named, or that the literature points to, are now provably
  excluded.
- **Full proofs:** `research/artifacts/guba-sapir-normal-forms-not-automatic-2026-09-16.md`.
- **Scripts:** `experiments/thompson-f-guba-sapir-ftp-2026-09-16/`.

## Setup

The hole asks for an automatic structure on some finite generating set of `F`.
By the standard facts in the root, over `A = {x0^±1, x1^±1}` this means a
regular language mapping onto `F` with the synchronous fellow traveller
property. Before this lane, the Attempts section recorded:

- geodesic and near-geodesic languages over `A` are dead (Cleary–Elder–Taback;
  Belk as cited by Hauze; Hauze Theorem 1.1, imported as
  `thompson-f-has-no-near-geodesic-automatic-structure`);
- the standard infinite normal form rewritten over `x0, x1` was expected to fail
  because right multiplication by `x0` shifts indices, with no proof recorded;
- forest-diagram tours were an observation only.

The most natural candidate not yet examined was the regular set of Guba–Sapir
normal forms. CGHJS use it for their autostackable structure, and it is not
near-geodesic, so Hauze's theorem says nothing about it.

## Status gate (checked 2026-09-16)

- **Zaremsky, "Some open problems"**, version dated July 12, 2026, fetched and
  read 2026-09-16. Section 2 item 2, "Is F automatic?", has no solved mark.
  Section 4 item 1 (amenable and automatic implies contractible Rips complex?)
  is also unmarked.
- **CGHJS, arXiv:1811.11691v1**, fetched. The abstract says "it remains unknown
  whether F is automatic". Section 1 displays the definition of `N` used here.
- **Hauze, arXiv:1801.01965**, fetched. Theorem 1.1 is the near-geodesic
  exclusion already imported into the graph.
- **arXiv API searches over https**, 2026-09-16:
  - `ti:"Thompson's group F"`, newest first, listed through arXiv:2609.14702
    (2026-09-13). No title claims automaticity or non-automaticity.
  - `abs:"Thompson" AND abs:"fellow traveller"` and `... "fellow traveler"`:
    no hits.
  - `abs:"regular language"` with Thompson: only older papers, none resolving
    the question.
  - Queries for "biautomatic" and "combable" failed with connection resets and
    were not retried successfully. Treat that part of the gate as incomplete.
- **AIM, "Thompson's Group at 40 Years, Preliminary Problem List"** (AIM
  Research Conference Center, January 2004). The text was downloaded this
  session from aimath.org, but a re-fetch to confirm the exact URL failed with a
  connection reset. Q 4.2 reads "Is F automatic? Synchronously or asynchronously
  combable? What languages are associated with F? Guba and Sapir give an example
  of a nongeodesic language." This is background only.

Conclusion of the gate: the problem is open as of 2026-09-16, as far as these
sources show.

## What was proven

### Claim 1: `thompson-f-guba-sapir-normal-forms-not-automatic`

Route `thompson-f-guba-sapir-normal-forms-not-automatic-proof`, `requires: []`.
Full proof in artifact §1–§6.

- `N` is the set of freely reduced words over `A`, with `x = x0` and `y = x1`,
  containing no subword `y^ε x^i y` and no subword `y^ε x^(i+1) y^-1` for
  `i >= 1` (CGHJS §1).
- The words `u_L = y x^L` and `v_L = x^L y x^-(L+1) y x^(L+1)` lie in `N`, and
  `u_L y = v_L` in `F`. This is the relation `x_1^-1 x_n x_1 = x_(n+1)` for
  `n >= 2`, derived in artifact §1 from the two CFP relators.
- **Theorem.** With `a = floor(L/2)`, the vertex `y x^a` of the path of `u_L`
  is at distance at least `(a - 1)/2` from every vertex of the path of `v_L`.
- **Lemma D** (artifact §4). In a synchronous or asynchronous automatic
  structure over `A`, accepted `u, v` with `ū s = v̄` for a generator `s` have
  paths within Hausdorff distance `2 max_s |V_s| + 1`. The proof completes a
  partial accepting run along a shortest path in the finite state graph, with
  end-of-tape flags in the asynchronous case.
- **Corollary.** No language over `A` containing `u_L, v_L` for infinitely many
  `L` is the language of a synchronous or asynchronous automatic structure. In
  particular `N` and every superset of `N` over `A` are excluded. Granting the
  uniqueness theorem of Guba–Sapir (1997, Theorem 2, not fetched, relayed by
  CGHJS §2.2), so is every sublanguage of `N` that maps onto `F`.

**Lower-bound machinery** (all applied to images of arbitrary words under the
PL action `ρ`, so faithfulness is never used):

- `α(h) = log2 ρ(h)'(0+)`, a homomorphism with `|h| >= |α(h)|`;
- Lemma A: `|h| >= D(ρ(h)) - 2`, where `D` is the largest dyadic depth of a
  breakpoint;
- persistence of breakpoints under composition, pulled back through powers of
  `X0` (Lemmas B and C).

Exact computations (`check_witnesses.py`) show the true distance is `a + 1` for
`L <= 15`, so the bound is not sharp but has the right order.

### Claim 2: `thompson-f-standard-normal-forms-not-automatic`

Route `thompson-f-standard-normal-forms-not-automatic-proof`, `requires: []`.
Full proof in artifact §7.

- `T` is the set of telescoped CFP standard normal forms: substitute
  `x_n = x^-(n-1) y x^(n-1)` and freely reduce.
- `s_n = x^-(n-1) y^-1 x^(n-1)` (from `x_n^-1`) and
  `t_n = y x^-n y^-1 x^n` (from `x_1 x_(n+1)^-1`) lie in `T`, and `s_n y = t_n`.
- The vertex `x^-(n-1)` of the path of `s_n` is at distance at least
  `(n - 2)/2` from the path of `t_n`.
- With Lemma D, no language over `A` containing infinitely many of these pairs
  is automatic (synchronous or asynchronous). This covers `T`, whether or not
  `T` is regular. Regularity of `T` was not examined.

### A correction to the Attempts on the hole

The Attempts entry on the standard normal form says right multiplication by `x0`
is what breaks fellow travelling. That is not so for `T`: the telescoped normal
form of `g x0` is the free reduction of the telescoped normal form of `g`
followed by `x` (artifact §7). The divergence comes from right multiplication
by `x1`, which acts as the conjugation `x_1^-1 x_n x_1 = x_(n+1)` and so
changes the front of the word.

## Approaches and where each dies

1. **Guba–Sapir normal forms `N`.** Dies at the Theorem of Claim 1. Right
   multiplication by `y` turns `y x^L` into a word that first travels to
   `x^L y x^-(L+1)` before returning, and the breakpoint depth of `ρ` certifies
   that the midpoint `y x^a` is far from that detour.
2. **Telescoped standard normal forms `T`.** Dies at Proposition 7.1 (Claim 2),
   by the same mechanism: `x_n^-1 y = y x_(n+1)^-1` puts a `y` at the front.
3. **Near-geodesic languages.** Already dead by Hauze. That theorem does not
   reach `N`: `|v_L| = 3L + 4` while `|ū_L y| <= L + 2`, so `N` has unbounded
   additive excess and an automatic structure containing `N` is not excluded by
   it. For `T`, the pair `(s_n, t_n)` has excess only `2`, and whether `T` has
   bounded additive excess was not examined. Claim 2 excludes every superset of
   `T` as well, and Hauze's theorem says nothing about supersets with unbounded
   excess, so Claim 2 is still not a consequence of it.
4. **Coarse invariants.** The quadratic Dehn function of `F` (Guba, Invent.
   Math. 2006, not fetched) and type `F_∞` are consistent with automaticity and
   give no obstruction. AIM Q 4.3 (2004) proposes proving that some
   higher-dimensional isoperimetric inequality of `F` is not Euclidean. The list
   states that automatic groups satisfy Euclidean isoperimetric inequalities in
   every dimension, so this would show `F` is not automatic. The present status
   of that line was not checked.
5. **Non-automatic via finite cohomological dimension.** The route
   `thompson-f-not-automatic-via-finite-cd` needs the open hole
   `torsion-free-automatic-groups-have-finite-cd`. The AIM list notes that no
   torsion-free infinite-dimensional automatic group is known, so this is a
   real but unresolved line. Not attacked in this lane.
6. **Graph automatic structures** (Elder–Taback, arXiv:1501.04313, as
   described in the Attempts; not re-fetched). Graph automaticity is a
   different notion from an ECHLPT automatic structure, and the 1-counter
   structure is built on the standard normal form. Claim 2 shows that its
   telescoped words over `A` cannot be the language of an automatic structure,
   so that structure does not upgrade directly.

**Lesson for later lanes.** Over `{x0, x1}` both natural normal forms put the
effect of right multiplication by `x1` at the front of the word. Any viable
language must localize that effect in a bounded suffix after reparametrization.
Claim 1 also shows this cannot happen by merely accepting `N`'s words together
with extra ones: a superset of `N` is excluded too. The same holds for
supersets of `T`. The forest-diagram tour idea in the Attempts meets the same
obstacle and would have to avoid both families of pairs.

The two exclusions are over the fixed alphabet `A`. A different finite
generating set changes the words, and Lemma D does not transfer across
generating sets for a fixed set of normal forms. Automaticity itself is
independent of the generating set, but the candidate language would then be
different.

## Suggestions for the referee (not done in this lane)

- Point the Attempts entries on `thompson-f-is-automatic` to the two new claims.
- Correct the `x0` remark in that entry, as explained above. The same remark
  appears in `research/artifacts/zp-thompson-f-automatic-2026-09-13.md` around
  lines 83–84.
- The weakest imported step is the exact form of the ECHLPT asynchronous
  definition behind Lemma D. The lemma is proved from the definition as recalled
  in artifact §4, but the book was not re-fetched and no theorem numbers are
  cited.

## Files and computations

- `research/thompson-f-guba-sapir-normal-forms-not-automatic.md` (claim).
- `research/thompson-f-guba-sapir-normal-forms-not-automatic-proof.md` (route,
  `requires: []`).
- `research/thompson-f-standard-normal-forms-not-automatic.md` (claim).
- `research/thompson-f-standard-normal-forms-not-automatic-proof.md` (route,
  `requires: []`).
- `research/artifacts/guba-sapir-normal-forms-not-automatic-2026-09-16.md`.
- `experiments/thompson-f-guba-sapir-ftp-2026-09-16/plf.py`: exact PL
  arithmetic over `Fraction`.
- `experiments/thompson-f-guba-sapir-ftp-2026-09-16/check_witnesses.py`, run as
  `timeout 600 python3 -B check_witnesses.py 30 8 10`. Output in
  `check_witnesses_output.txt`, `TOTAL FAILURES: 0`. It checks:
  - the relators;
  - the relation;
  - membership of `u_L, v_L` in `N`;
  - the depth lemmas;
  - the bound for `L <= 30`;
  - exact distances for `L <= 15`;
  - that the 48931 words of `N` of length at most 10 represent distinct
    elements.
- `experiments/thompson-f-guba-sapir-ftp-2026-09-16/check_tsnf.py`. Output in
  `check_tsnf_output.txt`, `TOTAL FAILURES: 0`, about 30 s. It checks:
  - the relation for `3 <= n <= 30`;
  - the vertex bounds of Claim 2 for all `k` when `n <= 12`;
  - the vertex bounds for `k = n - 1` when `n <= 30`.

No proof depends on the computations.

## Literature

- M. Zaremsky, *Some open problems* (July 12, 2026 version), fetched 2026-09-16.
- N. Corwin, G. Golan, S. Hermiller, A. Johnson, Z. Šunić, *Autostackability of
  Thompson's group F*, arXiv:1811.11691v1, fetched 2026-09-16.
- D. Hauze, dissertation, arXiv:1801.01965, fetched 2026-09-16.
- AIM, *Thompson's Group at 40 Years, Preliminary Problem List* (January 2004),
  text downloaded 2026-09-16; exact URL not re-confirmed.
- arXiv API title and abstract searches, 2026-09-16, listing through
  arXiv:2609.14702.
- V. Guba, M. Sapir, *The Dehn function and a regular set of normal forms for R.
  Thompson's group F*, J. Austral. Math. Soc. Ser. A 62 (1997). Not fetched;
  used only via CGHJS §2.2.
- J. Cannon, W. Floyd, W. Parry, *Introductory notes on Richard Thompson's
  groups*, Enseign. Math. 42 (1996). Not re-fetched.
- D. Epstein et al., *Word Processing in Groups* (1992). Not re-fetched.
- S. Cleary, M. Elder, J. Taback, arXiv:math/0410616, and M. Elder, J. Taback,
  arXiv:1501.04313. Cited from the existing Attempts section; not re-fetched in
  this lane.
