---
rg: 2
id: q2-a2-tilde-triangle-groups-are-not-left-orderable-proof
kind: route
title: Complete length-2 rewriting system plus positive-cone SAT on small balls excludes left orders on all Fano-plane triangle groups
target: q2-a2-tilde-triangle-groups-are-not-left-orderable
requires: []
artifacts: [experiments/a2-triangle-left-orders-2026-09-17/enum_q2.py, experiments/a2-triangle-left-orders-2026-09-17/q2_presentations.json, experiments/a2-triangle-left-orders-2026-09-17/q2_classes.out, experiments/a2-triangle-left-orders-2026-09-17/color1.py, experiments/a2-triangle-left-orders-2026-09-17/kb.py, experiments/a2-triangle-left-orders-2026-09-17/lo_sat.py, experiments/a2-triangle-left-orders-2026-09-17/calib.py, experiments/a2-triangle-left-orders-2026-09-17/lo_sat_q2.out, experiments/a2-triangle-left-orders-2026-09-17/lowidx7.g, experiments/a2-triangle-left-orders-2026-09-17/quotients7.txt, experiments/a2-triangle-left-orders-2026-09-17/quotients7.json, experiments/a2-triangle-left-orders-2026-09-17/lo_sat_sub.py, experiments/a2-triangle-left-orders-2026-09-17/sub_r3.out, experiments/a2-triangle-left-orders-2026-09-17/sub_r4.py, experiments/a2-triangle-left-orders-2026-09-17/sub_r4.out, experiments/a2-triangle-left-orders-2026-09-17/cyclic_tp.py]
---

All scripts are in `experiments/a2-triangle-left-orders-2026-09-17/`. Each runs in seconds.

**Step 1: enumeration** (`enum_q2.py`). The Fano plane has lines `{i, i+1, i+3} mod 7`.
The script loops over all `7!` bijections `λ`. For each, it solves the exact-cover problem
"every incident pair `(x,y)` with `y ∈ λ(x)` lies in exactly one cyclic class", and closes
under rotation. The candidate triples are exactly those with `y ∈ λ(x)`, `z ∈ λ(y)`, `x ∈ λ(z)`.
This gives 744 presentations. Canonicalising over all `7!` relabelings leaves 11 classes. The
classes are listed in `q2_classes.out`, and seven are torsion-free.

A classification of the triangle presentations themselves does not matter for the theorem. A
presentation missed by the enumeration would be a gap, but the search is exhaustive over `λ`
and `T`.

**Step 2: word problem** (`kb.py`, `check_confluent` in `lo_sat.py`).

- Letters are `a_x` and `A_x = a_x^{-1}`.
- The initial rules are the free cancellations, plus `u → v^{-1}`, oriented shortlex, for
  every factorisation `uv` of every rotation of each relator and of its inverse.
- One completion round adds the length-2 to length-2 critical-pair rules. The system then has
  98 rules, all with left sides of length 2.
- `check_confluent` reduces both sides of every overlap `l_1 = s t`, `l_2 = t u` with `|t| = 1`.
  They always agree. Length-2 left sides admit no inclusion overlaps, and every rule strictly
  decreases in shortlex order, so the system terminates.
- By Newman's lemma it is complete. Every rule is a consequence of the relators and every
  relator reduces to the empty word, so the rule congruence equals the group congruence.
- Hence distinct normal words are distinct elements, and a nonempty normal word is `≠ 1`.

Sanity check: the numbers of normal words of lengths 1, 2, 3 are 14, 98, 560. These equal
the number of vertices at combinatorial distance 1, 2, 3 in an A~_2 building of order 2,
computed from shapes `(m,n)`. For example `560 = 2·7·16 + 2·7·6·4`.

**Step 3: positive cone on a ball** (`lo_sat.py`).

- Take the normal words of length at most `r`, with a Boolean `p_g` for each `g ≠ 1`.
- Add clauses `p_g ⊕ p_{g^{-1}}`.
- For all `g, h` in the ball with `gh` in the ball, add `¬p_g ∨ ¬p_h ∨ p_{gh}`. If `gh = 1`,
  add `¬p_g ∨ ¬p_h`.
- A left order `<` on `Γ_T` gives the solution `p_g = [g > 1]`. The first clauses hold because
  `g ≠ 1`, and the second because the positive cone is a semigroup.
- So an unsatisfiable instance proves that `Γ_T` is not left-orderable.

Results (`lo_sat_q2.out`; CaDiCaL 1.5.3 and Glucose 4 agree on every instance):

- `r = 2` (113 elements, 2912 clauses): UNSAT for 0, 1, 2, 3, 5, 6, 7, 8, 9, 10; SAT for 4.
- `r = 3` (673 elements, 61824 clauses): UNSAT for 4.

**Step 4: hand proof for 5, 6, 9, 10** (`color1.py`). Suppose `<` is a left order. Put
`s(x) = +` if `a_x > 1` and `−` otherwise. Each relator class `xyz` gives `a_x a_y a_z = 1`,
so `x, y, z` cannot all have the same sign: a product of positive elements is positive, and
its inverse product of negatives is negative. `color1.py` finds no admissible `s` for 5, 6, 9, 10.

- For 9 and 10 the seven classes cover each of the 21 pairs of points exactly once, so they
  form a Fano plane, which has no proper 2-colouring.
- Groups 4, 7 and 8 have 6, 6 and 24 admissible sign patterns, so for them the certificate
  needs longer elements.

**Step 5: subgroups of index at most 7** (`lowidx7.g`, `lo_sat_sub.py`).

- `lowidx7.g` runs GAP's `LowIndexSubgroupsFpGroup(G, 7)` on the seven torsion-free groups.
  It returns one subgroup per conjugacy class, 85 nontrivial classes in all: 10, 7, 7, 10, 5,
  23, 23 for groups 4–10. The coset actions go to `quotients7.txt`, converted to `quotients7.json`.
- A conjugate of a left-orderable group is left-orderable, so one class representative suffices.
- `lo_sat_sub.py` checks that each relator acts trivially on the cosets. `H` is the stabiliser
  of coset 1, and a normal word `w` lies in `H` iff its letters, applied in order, fix 1.
- Variables are the nontrivial elements of `H ∩ B_r`. The clauses are the same as in Step 3,
  for pairs `g, h ∈ H ∩ B_r` with `gh ∈ B_r`. Soundness is the same argument, applied to the
  positive cone of `H`.
- Results (`sub_r3.out`): on `B_3`, 78 of the 85 classes are UNSAT.
- The 7 remaining classes (group 4: index 4, 6, 4, 4; group 7: index 6; group 8: index 4, 6)
  are UNSAT on `B_4` with up to 860 subgroup elements (`sub_r4.py`, `sub_r4.out`).
- Every subgroup is also torsion-free and a lattice on the same building, hence Kazhdan.

**Calibration** (`calib.py`, same code).

| group | ball | result | expected |
|---|---|---|---|
| `F_2` | `B_4` | SAT | left-orderable |
| `Z^2`, Klein bottle group | `B_4` | SAT | left-orderable |
| `Z/3` | — | UNSAT | torsion |

For groups whose rewriting system is not confluent, the script's element identification is
incomplete, and an UNSAT answer there is not a certificate. This happens for `Z^2`, Klein and
the Promislow-type test. Only confluent instances are used in this proof.

**Approach record.**

- *Why it can succeed where the dead approaches failed.* It does not need unipotent Heisenberg
  configurations (Witte Morris), linearity or boundary theory (Deroin–Hurtado). It uses the
  exact local combinatorics of the building's link.
- *Falsifiable first step.* Level-1 sign colourings, done in the first hour.
- *Calibration.* The free group and `Z^2` stay satisfiable, and torsion groups are refuted.
- *Scaling note.* `cyclic_tp.py` shows that no triangle presentation of order 4 is invariant
  under a Singer translation `Z/21`: `λ(x) = x + E` forces a 5-element `E` to be covered by
  zero-sum triples, and none exists. A SAT search over all `λ` (order 4, torsion-free, not
  landed) found none within 18 minutes. The order-4 case is left open.
