---
rg: 2
id: amenable-t-shape-schur-kernel-proof
kind: route
title: Asphericity over the torsion-free coefficient subgroup spreads to the ambient group, then Hopf
target: amenable-t-shape-adjunctions-kill-no-schur-class
requires: [torsion-free-amenable-t-shape-adjunctions-are-aspherical, aspherical-adjunction-has-zero-schur-kernel]
artifacts:
  - research/artifacts/kl-torsion-free-asphericity-pins-2026-09-13.md
---

Conjugating `w` in `Q * <t>` changes neither the group `(Q * <t>)/<<w>>` nor
the homotopy type of the cellular model (Bogley--Edjvet--Williams l.137), so
take `w` cyclically reduced. Its letters from `Q` lie in `B`, so `w` is also
cyclically reduced in `B * <t>` with the same `t`-shape.

1. By `torsion-free-amenable-t-shape-adjunctions-are-aspherical` applied to
   `B`, the relative presentation `P_0 = <B, t | w>` is aspherical in the
   Bogley--Pride sense, i.e. `pi_2(L(P_0), K(B,1)) = 0`.
2. The relator lies in `B * <t>`, so Bogley--Edjvet--Williams Lemma
   `Coefficient` (l.213–214) gives that `P = <Q, t | w>` is aspherical.
3. Their Lemma `KG1` (l.99–100) gives that `Q -> G(P) = (Q * <t>)/<<w>>` is
   injective and that `L(P) = (K(Q,1) v S^1) cup_w e^2` is a `K(G(P),1)`.
   This is items 1 and 2.
4. `aspherical-adjunction-has-zero-schur-kernel` applies to `L(P)` and gives
   item 3.

The three lemmas are quoted verbatim in the artifact. No step uses an
approximation property.
