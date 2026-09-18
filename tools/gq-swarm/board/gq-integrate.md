# gq-integrate — graph health for gq landings

**Role.** Idle until team-lead (address `main`) asks for a pass. Only lane allowed to run `bin/cairn check`, at most once
per pass and never alongside other heavy work.

**Each pass:**
1. `git log origin/main` for gq landings (see `$GQ/state/landed.log`); list which gq nodes are not in the shared checkout
   yet, since `bin/cairn check` reads the checkout.
2. `bin/cairn check` once in /Users/user/nonsofic_existence; triage any errors or warnings on gq nodes (bad ids,
   missing `distinct_from`, dangling requires/targets/artifacts).
3. Fix lint by relanding corrected copies through `$GQ/gqland.sh gq-integrate …` with `GQ_BASE=<sha>`.
4. Wire routes to `gl-n-q-embeds-in-fp-simple-group` wherever lanes forgot to.
5. Land `research/artifacts/gq-gq-status.md`, then SendMessage team-lead a short status.

**Pass 1 done (2026-09-17).** Status artifact `research/artifacts/gq-gq-status.md` (ceecf6bb6). Fixes:
75cf1f5ae and 37f7ed114 (34 route titles), c1ec40220 (2 missing proof routes), 27deb1b9c (root O5/O6),
2603283c9 (root Attempts item 15, obstruction index). Every gq claim's stated status now matches the computed
status; the root computes OPEN.
**Pass 2 done (2026-09-18).** Text fixes 3befe79c8 (BS(1,3) nV wording, SMART renormalization pointer, char-0 ring PASS citations); status 45c4d9093. Open wiring for owners: capacity-chain proof route requires the refuted candidate (notation only); one-steinberg-group-contains-every-gl-n-q and sl2-casimir-cannot-separate-verma-from-finite-dimensional have no routes; gl-n-q-bh-via-leavitt-resolvent-units is dead (prerequisite REFUTED).
**Wiring fixes (2026-09-18, authorized):** 44d170eda capacity-chain proof route requires: []; f8939e185 one-steinberg proof route (requires corrected by its owner in 25af0bf58); a3abd895f sl2-casimir proof route; db1a5e448 dead Leavitt-resolvent route recorded in the route and in root Attempts item 19. Recomputed at 25af0bf58: all four targets ESTABLISHED as stated; root G OPEN; Problem 2.7 root ESTABLISHED through four routes.
**Needs:** RULES §4 route template and gqland.sh lint should require `title:`, or untitled routes keep coming.
**Dead:** none.
**Sparks:** none.
