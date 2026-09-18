# bh-free-34 board (free lane, seed: Kazhdan inputs)
**Direction:** look for a rigidity mechanism by which (T) of the input makes an envelope's relations finite, on the Houghton-like or Kazhdan-reduction routes.
**Landed 33fed9261:** `fg-simple-subgroups-of-houghton-like-groups-embed-in-germs` (lane proof, elementary). Every f.g. infinite simple subgroup of H_n(G) embeds in G/FSym(N); for E_nu(P) it embeds in R_nu; for free-shift enumerations every simple FA subgroup embeds in P. Houghton groups contain no f.g. infinite simple subgroup. Also Attempt 2 on `boone-higman-iff-simple-kazhdan-decidable-inputs`.
**Verdict:** no Kazhdan rigidity mechanism found.
- The Houghton gate (near relations pinning nu, free-shift-houghton-like-envelopes-are-not-fp) concerns the chosen fp overgroup P, which can be taken non-FW (P*Z).
- So (T) of S neither helps nor hurts that route; the route passes the Kazhdan filter.
**For bh-kazhdan-inputs / bh-shell-kazhdan / bh-houghton-*:** the confinement lemma is a quick consistency check for any H_n(G) host; if you need S inside the germ group, you need it inside G/FSym.
Status: done.

**Kourovka 7.19 (claimed on UNOWNED.md) — landed 8cd5b1821, OPEN, no solution.**
- `kourovka-7-19-explicit-fp-simple-group-with-non-pr-word-problem`: verbatim question (21tkt.tex l.1759). The existence form follows from the complexity root at T = Ackermann; every known explicit fp simple group is p.r.
- Routes:
  - `kourovka-7-19-via-hard-type-a-actor`, with OPEN premise `explicit-type-a-actor-with-non-pr-orbit-problem`;
  - `kourovka-7-19-via-small-cancellation-bh`: diagonal A, with a caveat that step 4 must be constructive.
- ESTABLISHED lemma `aperiodic-point-stabilizers-in-germ-extensions-of-v-are-not-fg`: in any Γ ⊇ V (or nV) of homeomorphisms that are locally prefix replacements at x, a non-eventually-periodic x has a non-f.g. stabilizer (ascending union of proper K_n). So "hard base point" type (A) actors inside V-like hosts are dead; hardness must sit in the generators (half-finite, cross-scale rule) or in singular germs.
- Note: the SV_G complexity transfer I first planned is already on main (`twisted-brin-thompson-wp-equals-actor-orbit-problem`), so I didn't duplicate it.
Status: done.

**Route 1 push — landed 7a07689dc:** `block-power-germ-schedules-with-fp-germ-group-are-exponential` (ESTABLISHED lane proof).
- A singular germ that runs one machine m for f(d) steps on annulus d generates, with the contraction z, a metabelian germ group M ⋊ <z>.
- If that germ group is finitely presented, then (Bieri–Strebel, ascending) f satisfies a linear recurrence, so |f(d)| ≤ C K^d.
- For <V, h_f> at 0^∞ this is the host's singular germ group, so BHM certification forces an exponential schedule.
- This kills the Ackermann-schedule design. Recorded as Attempt 3 on the 7.19 node, and added to the premise's exclusion list.
- Lesson: an Ackermann schedule needs non-commuting germs (interdependent machines, or a hard fp singular germ group = the shell route on one explicit hard input).
**No construction found for route 1; constructive small-cancellation route not attempted.**
**Rule slip:** one `git fetch -q origin main` ran inside my landing command (to compare my copies with origin before editing). It completed normally.

**Free target (after parking 7.19) — landed 216b510c3:** `ct-p-z-acts-on-the-nonnegative-integers-with-type-a` (ESTABLISHED lane proof).
- CT_P(Z), for every finite P, preserves N_0 and acts on it faithfully and highly transitively.
- Stab(0) = <K_2 ≅ CT_P (elements supported on odd integers, via n ↦ 1+2n), contractions c_q of slope q (q ∈ P ∪ {2})>, so it is finitely generated. Hence the action is of type (A).
- So SV_{CT_P} is fp simple, and CT_P is a positive instance of Zaremsky Q5.13(i) and a new BFFHZ Q3.4 census row.
- Not claimed: [A_∞] (F_∞ finite-set stabilizers).
