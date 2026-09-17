---
rg: 2
id: sofic-groups-are-quantum-surjunctive
kind: claim
title: Over a sofic group every equivariant finite-propagation unital *-endomorphism of the quasi-local matrix algebra is onto
distinct_from:
  sofic-groups-are-surjunctive: that is the Gromov-Weiss theorem for classical cellular automata on full shifts; this is the quantum analogue for *-endomorphisms of the tensor product of matrix algebras, proved by packing translates of the local defect algebra into a relative commutant, with no pattern counting.
  amenable-groups-satisfy-the-garden-of-eden-theorem: that is the classical Moore-Myhill theorem; this covers amenable groups only as a special case of the sofic statement, and it concerns only injective versus onto (injectivity is automatic here).
  quantum-surjunctivity-conjecture: that is the statement for every group; this proves it on sofic groups.
artifacts:
  - experiments/quantum-surjunctivity-2026-09-17/clifford_star_f2.py
  - experiments/quantum-surjunctivity-2026-09-17/clifford_star_f2-output.txt
---

**ESTABLISHED** (route `sofic-groups-are-quantum-surjunctive-proof`).

Let `G` be a sofic group and `d >= 2`. Let `Phi` be a unital *-endomorphism of `A = (x)_G M_d` that commutes with
the shift and has `Phi(A_e) <= A_N` for a finite `N`. Then `Phi` is an automorphism, and its inverse is again
equivariant.

**Coverage.**
- This holds for amenable groups, residually finite groups, and in particular for `F_2`.
- Steps 2 and 3 of playbook lane (a) are therefore settled. Connes-Stormer entropy is not needed: the same
  relative-commutant count works along Folner sets.
- The search on `F_2` with `d = 2` and propagation `{1, a, b}` cannot find a strict solution. The artifact
  script confirms the Clifford sector of that search for `p = 2, 3, 5`.

**Proof idea.**
- A strict `Phi` has a nonzero local defect algebra `F`, of dimension at least 2, inside the relative commutant
  (`quantum-endomorphisms-split-off-their-relative-commutant`).
- On a sofic model `V`, the local rule gives a unital *-embedding of `(x)_(V_1) M_d` into `(x)_V M_d`, where `V_1`
  is the set of good points. Its relative commutant has dimension at most `d^(2 eps |V|)`.
- That commutant nevertheless contains the tensor product of `(1 - eps)|V| / |N^-1 N|^2` disjoint copies of `F`.
  This forces `2^(c|V|) <= d^(2 eps |V|)`, which fails for small `eps`.

**Referee (2026-09-17, ref-04): sound.**
- Checked every step of `sofic-groups-are-quantum-surjunctive-proof`. The good-point identities `(v.g).h = v.(gh)`
  and `w = v.h` with `h` in `N N^-1`, `W N^-1` or `W W^-1` use multiplicativity only on `K = (N u N^-1)^8`. The
  chart identity `iota_w = iota_v o alpha_h` makes `Psi` a unital *-homomorphism, the commutant bound is exact
  (`C = M_(d^(|V| - |V_1|))`), each `F_v` commutes with every `Psi_w(M_d)` by equivariance of the defect, and the
  packing bound `|V_1| <= |P| |W|^2` together with `dim F >= 2` contradicts the choice of `eps`.
- The route uses only items 2-3 of `quantum-endomorphisms-split-off-their-relative-commutant` (local defect and
  criterion), which the audit found sound. That node's Step 4 gap is now filled, so the derivation is complete.
- Literature: this is the quantum analogue of Gromov-Weiss (`sofic-groups-are-surjunctive`); for `G = Z` it is
  contained in Schumacher-Werner (quant-ph/0405174). No source stating the sofic case for quantum automata was
  found, and the claim does not assert more than the route proves.
