# Zaremsky Problem 3.10: Out(F_m) and closed-surface MCG into Aut(F_n) or Out(F_n)

Lane `z3-10-out-aut-embed`, ZP swarm, 2026-09-13. Root:
`zaremsky-3-10-out-fm-embeds-in-aut-fn`.

## 0. The problem

Zaremsky, *Some open problems* (July 12, 2026), Section 3, Problem 10, verbatim:
"(Added 3/20/25) Does every Out(Fm) embed in some Aut(Fn)? Does every MCG(Sg)
embed in some Out(Fn) and/or some Aut(Fn)?"

Reading used in Cairn:
- three part questions, (a) Out(F_m) into some Aut(F_n), (b) closed MCG(S_g) into
  some Out(F_n), (c) closed MCG(S_g) into some Aut(F_n);
- `S_g` closed, since surfaces with a puncture or boundary are already known to
  embed (Section 2);
- "embed" = injective homomorphism; `m, g ≥ 0`.

Context: BFFHZ, arXiv:2503.21882 (March 2025), prove the Boone--Higman conjecture
for Aut(F_n) and for mapping class groups of surfaces with punctures, boundary or
genus ≤ 2, and leave Out(F_n), n ≥ 3, and closed surfaces of genus ≥ 3 open. An
embedding into some Aut(F_n) settles those cases.

## 1. Status search (bounded)

- WebSearch was exhausted for this session; the arXiv API returned HTTP 429 or
  timed out on two queries on 2026-09-13.
- The ZP status table `zp-open-status-sections-2-4-2026-09-13-part2.md` found
  nothing deciding either question. The BH lanes' arXiv API queries on
  2026-09-12 found nothing on virtual splitting of `Aut(F_n) → Out(F_n)`.
- **Correction to that table.** It attributes "homomorphisms from closed-surface
  MCG(S_g) to Aut(F_n) or Out(F_n) are trivial for n ≤ 2g − 1" to arXiv:1608.03868
  (marked "not read"). That id is Bou-Rabee--Leininger, "Quotients of mapping class
  groups from Out(F_n)" (abstract read 2026-09-13), on finite quotients of mapping
  class groups; it does not state such a result. What is proved here is only the
  dimension bound for embeddings, `n ≥ 2g − 1`.

Verdict: open within the sources checked.

## 2. Established this pass (all elementary or imports; no novelty claimed)

1. `aut-free-embeddability-passes-to-finite-index-overgroups`.
   - If a finite-index subgroup `H` of `G` embeds in `Aut(A)`, then `G` embeds in
     `Aut` of the free product of `[G:H]` copies of `A` (induced action).
   - For free groups: `G` embeds in some `Aut(F_n)` iff some (every) finite-index
     subgroup does.
   - `Aut(F_n) ↪ Out(F_{n+1})`.
   - Out hosts do not pass up this way (factorwise-inner automorphisms).
2. `virtually-free-groups-embed-in-aut-free-groups`, e.g. `GL_2(Z) ↪ Aut(F_144)`.
3. `low-rank-out-free-groups-embed-in-aut-free-groups`: (a) holds for m ≤ 2.
4. `low-genus-closed-mcgs-embed-in-aut-free-groups`: (b) and (c) hold for g ≤ 2.
5. `punctured-surface-mcgs-virtually-embed-in-aut-free-groups`: import of the
   embedding steps of BFFHZ's proof of Corollary B.
6. `rank-lower-bounds-for-free-group-hosts-of-out-fm-and-mcg`: hosts need `n ≥ m`,
   respectively `n ≥ 2g − 1` (vcd comparison).

## 3. Reductions recorded as routes

- (a) at rank m ≥ 3 ⟺ `out-free-groups-virtually-embed-in-aut-free-groups`
  (routes `out-fm-aut-embedding-via-virtual-embedding`,
  `out-fn-virtual-embedding-from-full-embedding`).
- (c) ⇒ (b) (`closed-mcg-out-embedding-via-aut-embedding`), and no-(b) ⇒ no-(c)
  (`closed-mcg-no-aut-embedding-via-no-out-embedding`).
- `closed-mcgs-virtually-embed-in-punctured-mcgs` ⇒ (c)
  (`closed-mcg-aut-embedding-via-punctured-host`).
- (c) ⇒ Boone--Higman for closed-surface MCG (`closed-mcg-bh-via-aut-free-host`).

## 4. What the lemma changes

- **Torsion is irrelevant for (a) and (c).** Finite subgroups, their orders and
  normalizers cannot obstruct by themselves, since only a finite-index subgroup
  matters. For example, Out(F_2) does not look like a subgroup of Aut(F_2)
  (finite-subgroup realization; not claimed in Cairn), but it embeds in Aut(F_144).
  Obstructions must be virtual invariants.
- **Constructions may be unrelated to the outer action.** The BH region shows that
  lifts of the outer action, and homomorphisms preserving a free splitting with an
  `F_m` factor, are virtual sections of `Aut(F_m) → Out(F_m)` (for FA subgroups,
  m ≥ 4). The lemma allows any faithful action of any finite-index subgroup on any
  finitely generated free group, so those no-go results do not bound (a) or (c).

## 5. Sharpest open cruxes

1. **Positive (a), first test case m = 3.** Find a finite-index `L ≤ Out(F_3)` and a
   faithful action of `L` on a finitely generated free group. Candidates: a virtual
   section of `Aut(F_3) → Out(F_3)`; actions from finite covers that do not lift the
   outer action.
2. **Negative (a) or (c).** A property of every finite-index subgroup of `Out(F_m)`
   or `MCG(S_g)` that no subgroup of any `Aut(F_n)` has. Dimension gives only rank
   bounds, and Kazhdan's property (T) is shared by `Aut(F_n)`, `n ≥ 4`.
3. **(b) without (c).** Out hosts may allow constructions with no Aut analogue; and
   torsion can still matter there, since the induction lemma fails for Out.
