# bh-invent-18 (inventor, free choice) — 2026-09-18
**Approach.** Local emitter engines (input as isotropy at an infinite emitter), then collapse transfer as the obstruction. Signature: "collapse a deep subgroup into an edge stabilizer".
**Established.** 58db3f3f9 `stabilizer-engines-need-torsion-vertex-groups` (lane proof, not reviewed).
- F_B fp ⟹ every deep subgroup of B is normal; with isolation ⟹ none; so B is an fp torsion group with finitely many prime-order elements.
- F_V, F_T, F_F, Reid, and every B with an element of infinite order: not fp.
- Invalidates `isolated-vertex-groups-have-fp-stabilizer-engines`.
- Artifact `gq-bh-invent-18-collapse-transfer.md`: why BH must consume decidability via a non-local extension problem; bet = Track A with (★′) rigidity.
**Needs.** Referee of both 58db3f3f9 and bb487abce (they share the table-transport lemma). gq-referee-a was unreachable at 16:2x; the request went to team-lead. 378b1cf3e marks item 3(d) of bb487abce as superseded.
**Dead.** Stabilizer engines in free-product form, for every known infinite vertex group.
**Sparks.**
- Extend collapse transfer to A * B with A infinite and to amalgams A *_C B with infinitely many pair orbits on B/C. That would kill plain-boundary compression codings of Λ_1 * Z.
- Test whether the K-periodic fakes of finite-type blow-ups are always empty.
**Pass 2 (coordinator: positive construction for (★′)/SEED, non-local constraint consuming decidability).**
- Landed 9a9fed6b0 `anticipation-layers-convert-totality-into-isolation` (lane proof, not reviewed).
  - A label copied along a readable walk and fixed at halting sites is forced iff the walk is total. So a decorated seed stays isolated exactly when the algorithm halts everywhere, with the same stabilizer.
  - Quantum transport: F_t(q)Π = ΠF_t(end), so the layer is rigid on the terminating part.
  - Two far non-terminating basins kill rigidity (clustering lemma). Parallel walks in Z² die, even with trivial output.
- Decisive lemma CB (OPEN): a rigid seed with hard total outputs and convergent non-terminating basins. Anticipation never changes stabilizers, so it certifies but cannot create hard membership, and it does not by itself decide CAP.
**Pass 3 (CB: construct it or prove the tension).** Landed c1de03335 `rigid-seed-decorations-compute-only-where-rogue-walks-fill-space` (lane proof, not reviewed).
- Sufficient: rogue (non-halting) walks come near every site ⟹ rigid. Key: the base algebra is a quotient of Clop(Y_0).
- Necessary: a rogue basin far from another modification ⟹ not rigid.
- Z^d, d ≥ 2: periodic points must be mortal.
- CAP-type bounds: tree seeds of free products of finite and cyclic groups ⟹ decorations regular (Büchi pre*); C_Z⊠C_Z product seed ⟹ rigid total decorations finite-state.
- CB now lives only on aperiodic bases with space-filling rogue walks. Design rule for the machine rung: rogue runs sweep K_M.
