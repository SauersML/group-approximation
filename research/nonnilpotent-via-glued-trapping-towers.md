---
rg: 2
id: nonnilpotent-via-glued-trapping-towers
kind: route
title: Glue one trapping tower per depth into one simple inductive system, so visible seeds of every depth give a non-nilpotent component group
target: simple-cstar-unitary-component-group-not-nilpotent
requires:
  - unitary-word-transfer-to-simple-ah-via-trapping
  - trappable-unitary-commutator-seeds-of-every-depth
artifacts:
  - research/artifacts/class-four-lambda-mod-eight-trapping-part3-2026-09-13.md
---

Part 3, Proposition 9.1.

Stage n is the direct sum of towers T_c for 2 <= c <= n, plus two auxiliary
summands of consecutive ranks. The auxiliary summands keep the gcd of the
ranks equal to one, so every large rank can be realized.

Tower T_c enters at stage c as C(M_c, M_{N_c}), with N_c in S_c large enough.
It has X = point and protected block C^{N_c}. From then on it evolves by the
transfer theorem's steps Gr_{m_c}(H^{m_c + N_c d}).

Every summand receives dense evaluation blocks from every earlier summand,
tensored with its own step bundle. So the limit is simple (Toms Lemma 6.3).
The evaluation blocks only enlarge d, so each T_c keeps its count ±1 and its
Spin_{m_c}-structure. The c-fold witness of T_c stays detected in T_c. Its
images in the other summands contract. By Toms Lemma 7.1 it stays outside U_0
of the limit, so gamma_c != 1 for every c.

The seed prerequisite is open, and it may be false; see its Attempts.
