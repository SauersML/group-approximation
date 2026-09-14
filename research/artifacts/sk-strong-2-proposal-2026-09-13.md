# sk-strong-2 proposal (2026-09-13): no change to the note, one optional clause

Lens: a construction giving more properties at once.

## Result
- **No different construction was found that adds a property to "infinite, simple, Kazhdan, LEF" with a proof as short.** Three firewalls explain why:
  - LEF rules out finite presentation (Vershik–Gordon).
  - EL_n over these rings always has torsion.
  - LEF with small-rank roots rules out uniform simplicity (new node `subshift-elementary-groups-are-not-uniformly-simple`).
- **The same group already has many properties.** `subshift-elementary-group-properties-at-once` collects them: simple, (T), a marked limit of SL_{3N}(F_2) expanders, three torsion generators, all finite groups and [[T]]' inside, not uniformly simple, unique trace.
- **New:** not uniformly simple, established (fe3a1ff47d, unreviewed). Unique trace, routine via BKKO.
- **Open:** C*-simplicity, with Attempts on main.

## For the note
(a)–(e) of RULES §6 for the optional clause:
- (a) Position: in rev2's operator-algebra paragraph, after the Kirchberg/LLP sentence. Proposed text: `Every tracial state on $C^*_r(G_X)$ is the canonical trace, since the amenable radical of the simple nonamenable group $G_X$ is trivial~\cite[Theorem~4.1]{BKKO}.`
- (b) Proof: the clause is its own proof.
- (c) Length: +2 lines, plus a BKKO bibitem (+4).
- (d) Reader trade-off: a true, short, routine consequence. It adds one citation, and it makes no theorem stronger in a way the note needs. **Recommendation: skip it** unless the operator-algebra paragraph wants completeness.
- (e) Status: unreviewed; queued with sk-verify-5.

Non-uniform simplicity and C*-simplicity stay in Cairn.
