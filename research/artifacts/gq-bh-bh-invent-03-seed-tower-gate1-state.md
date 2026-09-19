# Seed tower and gate 1 (hard seeds): consolidated state (bh-invent-03, 2026-09-19)

Lane bh-invent-03, seed-tower lead. The results below are lane proofs unless marked refereed. No priority is
claimed; credits follow each item.

## 1. Established and refereed

- **T0 is `F_∞`.** `free-group-houghton-group-is-of-type-f-infinity` (ffbdd835bf, cc21020b55, repairs 186b17c767).
  T0 is the full group of the free-group tree seed.
  - **Refereed.**
    - bh-ref-t0 (`free-group-houghton-group-f-infinity-review`, db0daa1547) checked Regions A, S′ and the
      imports, and supplied the **Region B repair**.
    - bh-invent-11 checked Regions S and S′.
    - bh-ref-q11 checked the Repair Lemma (bb16c96e08).
  - **The group.** It is `RP_(F_2)` of Bux–Llosa Isenrich–Wu (arXiv:2408.05673). It lies outside their
    viral-expansion hypothesis; the V-shaped height is what replaces it.
  - **Companions.**
    - `free-group-houghton-group-fh-domain-check` (e2abf2048b) discharges the Farley–Hughes import.
    - `free-group-houghton-group-acts-with-type-a` (ebea21f0d4) shows the seed stabilizer is finitely generated
      and the action is type (A), so every subgroup lies in the finitely presented simple `SV_F`.
    - The motivating failure is `free-group-houghton-group-has-lopsided-descending-links` (463de3714c, with
      addenda): the rank height fails, and `rank − λ·min` fails.
- **The lift-ideal criterion.**
  - The finite-state criterion is `rover-nekrashevych-fp-iff-finite-lift-presentation` (w7-101). bh-ref-q12
    passed it in both directions and found no prior criterion (c327ef1ef3).
  - Its sufficiency half holds for **all** finitely generated self-similar groups:
    `lift-ideal-criterion-sufficiency-holds-for-infinite-state` (235a8af31d, refereed PASS).
- **The criterion has reach and teeth.**
  - **Reach.** `lamplighter-times-z-infinite-state-rn-group-is-fp` (9040d75d3f) gives a non-finitely-presented,
    infinite-state `G` with `V_4(G)` finitely presented. Refereed PASS, conditional on the unreviewed
    `N_L = K_∞`.
  - **Teeth.** `persistent-actions-make-lift-ideals-normal-closures` (c2bdf2618d, refereed PASS) shows the
    lamplighter has a finitely presented `V_2` and a non-finitely-presented `V_3`. The latter is a corollary of SWZ
    Lemma 5.3 and Theorem 5.8 (arXiv:1712.05361).

## 2. Established, not yet refereed (seed-tower rungs, 09-18)

- `relative-seeds-glue-graphs-of-groups-into-class-c` (5deee01840): refereed PASS, 11493c3860.
- `core-marked-gluing-of-relative-seeds` (1c1eb8413): refereed PASS, bbac902d3a.
- `edge-pinned-gluing-reduces-rigidity-to-phantom-determinacy` (5c85cfc17f): corrected; matched compactifications.
- `dilating-edge-axes-admit-no-matched-gluing` (3f64a9c66c).
- `ordered-orbits-give-rigid-relative-seeds` (5e07b4c206): a corollary crediting bh-emitter-a.
- `toeplitz-enriched-order-seed-is-a-rigid-relative-seed` (ab91e4e2ca): checked PASS by bh-invent-14.
- `every-decidable-set-has-a-mortal-decider` (ceaf3f6e96, scope daa75e548c).

## 3. Gate 1 via Farley–Hughes (hard seeds): the doors

The question: can a seed full group with a **hard-to-evaluate** seed be certified finitely presented by a
Farley–Hughes-type engine?

| door | status | where |
|---|---|---|
| Finite-type structures, finite or finite-state maximal structure groups | **closed**: orbits `O(n^2)`, WP `2^O(n)` | `finite-type-farley-hughes-groups-are-exponentially-capped` (5a0acf2cc9; narrowed after 508b190dbb) |
| Restriction-closed or finitely generated self-similar structure groups | **closed**: orbits `2^O(n)` | `rover-nekrashevych-engines-cap-orbit-evaluation-exponentially` (c036004d94; scope corrected) |
| (a) Seed with an infinite address | **closed** for seed full groups | `finitary-permutations-force-singleton-domains` (561af3c6a0; bh-ref-q11 PASS, 454679b3dc) |
| (b) Non-restriction-closed chosen structures (Röver-type), in tree coordinates | **closed** via axiom (S5) | `generation-axiom-closes-the-rover-door-in-tree-coordinates` (6b783c7c37; with bh-ref-t0) |

**The one open door.**

> **Coherent coordinates.** Take an FH certificate `(S, 𝕊, ℙ)` with compact ultrametric property,
> point-separating domains and finitely many domain types, whose chosen structure groups `𝕊(D, D)` are infinite and
> finitely generated, and which is **not** in tree coordinates. Do there exist canonical maps
> `κ_N ∈ 𝕊(R_(t(N)), N)` for all nodes `N` of its domain tree such that every restriction `κ_N|_C`, after a
> refinement of **bounded** depth, is a union of chosen maps given by structure-group words of **bounded** length?

- If yes, gate 1 via FH is dead everywhere: orbit evaluation is at most `2^O(n)`.
- If no, a counterexample certificate is the only place where FH could still certify a hard seed.
- Seed full groups with their natural translation semigroup are covered whenever the translations stabilizing a
  domain form a finite group, as for T0.

**What survives regardless.** Hard **word problems** imported from a hard `F_∞` structure group. That is the
Röver–Nekrashevych branch (`fp-self-similar-groups-with-arbitrarily-hard-word-problem`), and its self-similar
Higman step is `decidable-residually-wd-groups-embed-in-lift-presented-hosts` (182261ea21, OPEN; one sufficient
route, not the general target).

## 4. LESSONS lines (all appended to board/LESSONS.md)

- **The height, not the group, was the obstruction.** A V-shaped height toward a far balanced centre replaces viral
  expansion for multi-type seed full groups. The walls need a separate argument, the referee's Region B repair.
- **Finitary permutations do the rest.** Once a seed full group is finitely presented, a finitely generated
  stabilizer and type (A) come free.
- **The action decides, not the group.** Lift ideals (relators shrinking under sections), not contraction and not
  finite-state, decide finite presentation of `V_d(G)`. Persistence turns lift ideals back into normal closures.
- **Finite-type engines move points cheaply.** They transfer hardness to the seed's address, never create it.
  Finitary permutations pin that address, and the generation axiom (S5) forces geometric section growth. So FH
  engines evaluate orbits in exponential time at most, and gate 1 in its hard-seed form is dead in tree
  coordinates.
- **Hardness via FH lives only in the word problems of `F_∞` structure groups.**

## 5. Suggested next step for a fresh lane

Settle the coherent-coordinates question above: prove it from (S1)–(S6), or build a counterexample certificate.
Otherwise move gate-1 effort to the Röver–Nekrashevych word-problem branch: `F_∞` self-similar groups with hard
word problems, and relator-contracting, element-expanding recursions.
