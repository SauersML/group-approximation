---
rg: 2
id: binary-jacobson-el3-is-finitely-presented
kind: claim
title: The binary Jacobson elementary group EL_3 is finitely presented
distinct_from:
  jacobson-el4-is-finitely-presented-steinberg-group: that is rank four, where the Steinberg cover is finitely presented and K_2 vanishes; at rank three main has neither input.
  cohn-elementary-group-is-not-lef: that refutes LEF at ranks n >= 4 through a finitely presented cover; at rank three no finitely presented cover is known, and this claim would supply one.
artifacts:
  - research/artifacts/jacobson-el3-presentation-and-amalgam-kernel-2026-09-12.md
---

**OPEN.**

**Statement.** `E = EL_3(J)`, with `J = F_2<S,T | TS=1>`, is finitely presented.

**Why it matters.** If `E` is finitely presented, it is neither LEF nor LEA (artifact Proposition 4.1):
- every finite image kills the head `x_13(Q)` (`cohn-elementary-group-is-not-lef`, point 1);
- a finitely presented LEF group is residually finite;
- `E` is LEA only if it is LEF (`jacobson-elementary-groups-are-lea-only-if-lef`).

That rules out local embeddings for `binary-jacobson-el3-is-sofic`, but it does not decide soficity.

**Reductions (artifact Section 4).**
1. Main has no finite presentation of `St_3(J)`. `steinberg-finite-presentation-and-kazhdan-theorem` starts at rank
   four, and rank three lies below the quoted `K_2` stability range (`jacobson-el4-is-finitely-presented-steinberg-group`).
2. If `St_3(J)` is finitely presented, then `E` is finitely presented iff `K_2(3,J)` is finitely normally generated.
3. If `E` is finitely presented, then `SL_3(F_2[z^(±1)])` is finitely presented, since the symbol kernel is the normal
   closure of the head.
4. `E ≅ U / ker q` for the cone amalgam `U` (`jacobson-el3-amalgam-kernel-is-the-laurent-cone-kernel`). If `E` is
   finitely presented, then `ker q` is finitely normally generated in `U`.

## Attempts

* **Stable-range and amalgam reductions (w7-el3j-presentation, 2026-09-12).** Stops at rank three: neither a finite
  presentation nor an infinite family of independent relators was found.
  - The literature split, `SL_3(F_q[t])` not finitely presented against `SL_3(F_q[t^(±1)])` finitely presented, is not
    on main and is not used as a proof input.
  - Next: find either a marked sequence converging to `E` with no member a quotient of `E`, or finitely many relators
    whose normal closure in `U` is `ker q`.
* **Houghton frame (swarm-0917-w21-w21-ptm-break, 2026-09-20).** Source: `binary-jacobson-el3-contains-houghton-h3`.
  - The Levi compressor `d_12 = [[S,Q,0],[0,T,0],[0,0,1]]` is Houghton's translation on the three Fock rays. With
    its constant conjugate `d_13` it generates `H_3 <= E`, which is finitely presented (Brown 1987).
  - By `binary-jacobson-active-cycle-generates-rank-three`, `E` is a quotient of the finitely presented amalgam
    `A = (H_3 x| S_3) *_(S_3) SL_3(F_2)`. So this claim is equivalent to: `ker(A -> E)` is finitely normally
    generated. This replaces the non-finitely-presented cone amalgam `U` of reduction 4 by a finitely presented
    source.
  - First falsifiable test: do finitely many relators suffice? Take the relators "`x_ij(1)` commutes with a
    finitary permutation of disjoint support", together with lifts of a finite presentation of
    `SL_3(F_2[z^(±1)])`. Do they already force the image of `FSym(Omega)` to normally generate a locally finite
    subgroup?
  - Not decided; this is a reframing only. `H_3` is of type `F_2` but not `F_3`, which bounds nothing about `E`.
