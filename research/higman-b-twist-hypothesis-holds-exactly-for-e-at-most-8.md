---
rg: 2
id: higman-b-twist-hypothesis-holds-exactly-for-e-at-most-8
kind: claim
title: The B-tree kernel quotient of Gamma(3,2^e) is a finite self-similar 2-group of order 2^6, 2^9, 2^13, 2^17, 2^22 for e = 5..9, so Gamma(3,2^e) is reducible for e <= 9; the twist hypothesis (H_e) holds exactly for e <= 8; at e = 9 the normal closure of [a,c]^2 lies in A.<b^64,d^64>, giving an index-2^20 embedding of the edge image, and no 2-quotient of class <= 10 has ord(a) = 2^9
distinct_from:
  higman-gamma-3-2e-is-a-reducible-lattice-for-e-at-most-7: that proves reducibility for e <= 7 from permutation groups on balls of T_B, the reduction lemma under (H_e), and the failure of (H_e) for e >= 9, leaving e = 7, 8 open; this computes Bbar_e exactly through the self-similar word-tree model for e <= 9 (reducibility at e = 8, 9), settles (H_7) and (H_8), and replaces (H_e) at e = 9 by the minimal relative subgroup A.<b^64,d^64>.
  higman-edge-relator-twist-breaks-tree-lattice-freiheitssatz: that shows b^64 and d^64 lie in the edge image of Gammabar_e; this uses those two relations to bound ord(a) in all 2-quotients of class <= 10 at e = 9, and locates them inside Q_B as the four-valued defect group (Z/2)^2.
  higman-power-pair-collapse-is-base-uniform-up-to-torsion: that leaves open whether H4(3)/<<[a,c]^2>> has generators of infinite order; this does not settle that, and proves only ord(a) >= 2^7 for e >= 7 together with a class-10 ceiling of 2^8 at e = 9 for 2-quotients.
artifacts:
  - experiments/higman-b-automaton-2026-09-18/mult.py
  - experiments/higman-b-automaton-2026-09-18/check_ball.py
  - experiments/higman-b-automaton-2026-09-18/check_ball-output.txt
  - experiments/higman-b-automaton-2026-09-18/levels.py
  - experiments/higman-b-automaton-2026-09-18/levels_np.py
  - experiments/higman-b-automaton-2026-09-18/levels_ck.py
  - experiments/higman-b-automaton-2026-09-18/run9.sh
  - experiments/higman-b-automaton-2026-09-18/verify.py
  - experiments/higman-b-automaton-2026-09-18/verify_all.sh
  - experiments/higman-b-automaton-2026-09-18/verify_all-output.txt
  - experiments/higman-b-automaton-2026-09-18/lev8.out
  - experiments/higman-b-automaton-2026-09-18/lev9.out
  - experiments/higman-b-automaton-2026-09-18/rel.py
  - experiments/higman-b-automaton-2026-09-18/rel-e7-output.txt
  - experiments/higman-b-automaton-2026-09-18/rel-e8-output.txt
  - experiments/higman-b-automaton-2026-09-18/rel-e9-output.txt
  - experiments/higman-b-automaton-2026-09-18/symsec.py
  - experiments/higman-b-automaton-2026-09-18/symsec-output.txt
  - experiments/higman-b-automaton-2026-09-18/orbits.py
  - experiments/higman-b-automaton-2026-09-18/ord2.g
  - experiments/higman-b-automaton-2026-09-18/e567.out
  - experiments/higman-b-automaton-2026-09-18/e8.out
  - experiments/higman-b-automaton-2026-09-18/relators.py
  - experiments/higman-b-automaton-2026-09-18/abar_e5.g
  - experiments/higman-b-automaton-2026-09-18/abar_e6.g
  - experiments/higman-b-automaton-2026-09-18/qbexport.py
  - experiments/higman-b-automaton-2026-09-18/bbar_e5.g
  - experiments/higman-b-automaton-2026-09-18/bbar_e6.g
  - experiments/higman-b-automaton-2026-09-18/bbar_e7.g
  - experiments/higman-b-automaton-2026-09-18/qbpq.g
  - experiments/higman-b-automaton-2026-09-18/qbpq-e6.out
  - experiments/higman-b-automaton-2026-09-18/qbpq-e7.out
  - experiments/higman-b-automaton-2026-09-18/qbpq-e8.out
  - experiments/higman-b-automaton-2026-09-18/abarpq.g
  - experiments/higman-b-automaton-2026-09-18/abarpq-e7.out
  - experiments/higman-b-automaton-2026-09-18/abartest.g
  - experiments/higman-b-automaton-2026-09-18/abartest-e9-output.txt
  - experiments/higman-b-automaton-2026-09-18/abartest2-e9-output.txt
  - experiments/higman-b-automaton-2026-09-18/abartest10.g
  - experiments/higman-b-automaton-2026-09-18/abartest10-e10-output.txt
---

**ESTABLISHED** (proposed) by `higman-b-twist-hypothesis-holds-exactly-for-e-at-most-8-proof`.
- Lemmas 1–3 of the proof are proved by hand for every `e`. They reduce `Bbar_e` to a finite,
  exactly verified computation.
- Items 1–4 are proved from those computations: `verify.py`, `rel.py`, and the equality of two
  consecutive level orders.
- Items 5 and 6 are certified finite 2-quotient computations in GAP, combined with a hand
  argument.

**Setting.** As in `higman-gamma-3-2e-is-a-reducible-lattice-for-e-at-most-7` ("w13"):
- `Gamma_e = Gamma(3,2^e)`, `m = 2^e`, `n = m/4`, `t = 3^-1 mod m`;
- `A = <a,c>`, `B = <b,d>`, with `Gamma = A · B` exact;
- `Lambda_B` is the kernel on `T_B`, `Bbar = B/Lambda_B`, and `Q_B = Gamma/Lambda_B = A · Bbar`;
- `R = [a,c]^2`, `Gammabar_e = Gamma_e/<<R>>`, and `Qbar_B = Q_B/<<R>>`;
- `beta R beta^-1 = S_beta beta''`, with `S_beta in A` and `beta'' in B`;
- `(H_e)` is the hypothesis that `beta'' in Lambda_B` for all `beta`.

**Statement.**
1. **Bbar as a finite self-similar group.**
   - `B` acts on the `m`-ary word tree `W` by an explicit closed form. Its kernel there is
     `Lambda_B`.
   - `Bbar_e` is the stable level quotient `G_k` of this action (Lemma 3). The orders are:

     | e | 5 | 6 | 7 | 8 | 9 |
     |---|---|---|---|---|---|
     | `|Bbar_e|` | `2^6` | `2^9` | `2^13` | `2^17` | `2^22` |

   - `b` has order `m/4` in `Bbar_e`.
   - For `e = 6, 7, 8`, `Bbar_e` has nilpotency class `e - 4`, derived length 2 and exponent `m/4`
     (corroborated).
2. **Reducibility for e <= 9.** `Gamma(3,256)` and `Gamma(3,512)` are reducible lattices in
   `Aut(T_m) x Aut(T_m)`: `Lambda_A x Lambda_B` has index `2^34`, resp. `2^44`, and each factor is
   virtually free. With w13, `Gamma(3,2^e)` is reducible for every `e <= 9`.
3. **(H_e) holds if and only if e <= 8.**
   - `beta'' = 1` in `Bbar` for all `2^13`, resp. `2^17`, elements at `e = 7`, resp. `e = 8`.
   - Together with w13 (`e <= 6`, and failure for `e >= 9`), `(H_e)` holds exactly for `e <= 8`.
   - Hence for `e = 7, 8` the group `Abar_e = <a, c | a^m, c^m, S_beta>` embeds in `Qbar_B` with
     index `|Bbar_e|`.
   - The model gives `(b d)'' = b^(64v)` with `v` odd for `e = 9..16`.
4. **Relative Freiheitssatz at e = 9.** Put `u = b^64`, `v = d^64` and `Bbar_0 = <u,v>`.
   - `Bbar_0 ≅ (Z/2)^2`. It is central in `Bbar_9` and closed under `b <-> d` and under sections.
     It is the smallest such subgroup containing every `beta''`.
   - `beta''` takes the values `1, u, v, uv`, on `3·2^19, 2^19, 2^19, 3·2^19` elements.
   - `H = A · Bbar_0 = A ⋊ (Z/2)^2` is a subgroup of `Q_B`, with `u a u = a`, `u c u = c^257`,
     `v c v = c` and `v a v = a^257`.
   - `M = <<R>>_(Q_B)` is contained in `H`.
   - Hence the image `Abar^Q = H/M` of `A` in `Qbar_B` has index exactly `2^20 = |Bbar_9|/4`. It is
     2-generated, with the explicit presentation of proof §7(d): the twisted relators
     `S_beta w(beta'')`, where `w(beta'')` is one of `1, U, V, UV` with `U = S_(bd)^-1` and
     `V = sigma^2(S_(bd))^-1`, plus seven semidirect relations.
   - `ord(a)` in `Abar^Q` equals `ord(a)` in `Qbar_B`.
5. **Certificates and the lower bound.**
   - `Lambda_B` is the normal closure in `Gamma` of the relators of `Bbar`. So `Qbar_B` is an
     explicit quotient of `Gammabar_e`.
   - A 2-quotient of `Qbar_B` of class 11 and order `2^302` has `ord(a) = 2^7` at `e = 7`. At
     `e = 6` the corresponding quotient has class 9 and order `2^123`.
   - Consequently `ord(a in Gammabar_e) >= 2^7` for all `e >= 7`.
   - At `e = 8`, 2-quotients of `Qbar_B` of class up to 13 give only `2^7`.
6. **Class bound at e = 9.** Every 2-group quotient of `Gammabar_9` (or of `Qbar_B`, or of
   `Abar^Q`) of nilpotency class at most 10 has `ord(a) <= 2^8`. It is the `d`-side relation
   `d^64 = sigma^2(S_(bd))^-5` that caps it: with `b^64 = S_(bd)^-5` alone, class 9 already reaches
   `2^9`.

**What this does to the target question.** The target question asks for `ord(a) = 2^e` in
`Gammabar_e` for infinitely many `e`.
- The brief's step, "find `A · Bbar_0 ⊇ <<R>>` that still embeds", is done at `e = 9`. The answer
  is `Bbar_0 = <b^64, d^64> = (Z/2)^2`, which is minimal.
- The resulting embedding is exact. It yields an equivalent 2-generated problem of index
  `|Bbar|/4`, not a lower bound by itself.
- The tree kernels do not obstruct: `Gamma_e` stays reducible, and `Bbar` stays a finite 2-group,
  through `e = 9`.
- The obstruction is now arithmetic, on the pro-2 side. The first class at which a 2-quotient
  certifies `ord(a) = 2^e` grows: 9 at `e = 6`, 11 at `e = 7`, more than 13 in `Qbar_B` at `e = 8`,
  and more than 10 at `e = 9` (item 6).
- If the cap in item 6 persisted in every class, the residually-2 image of `Gammabar_9` would have
  `ord(a) <= 2^8`.

**Next step.** Decide whether `ord(a) = 2^8` persists in all 2-quotients of `Etest2`:
- run classes 11 and up with a larger budget, or run the standalone ANUPQ;
- run the `e = 10` analogue, with `(b d)'' = b^832` and its `d`-side mirror.

A permanent cap would mean that no finite 2-group quotient of `Gammabar_9` has `ord(a) = 2^9`. Any
proof of `ord(a) = 2^9` would then have to leave 2-groups. The w10 residually-2 tower of
`H4(3)/<<[a,c]^2>>` would also stop gaining a factor 2 at `e = 9`.

**Dead ends recorded here.** See proof §10:
- the hash search as proof;
- `Abar_e` 2-quotients at `e >= 7`;
- `Qbar_B` 2-quotients beyond class 13 at `e = 8`;
- `Etest2` beyond class 10.
