---
rg: 2
id: fpbs-mal-two-step-relative-position-rigidity-proof
kind: route
title: Transport both classes to hull translates in the Cayley tree and pin the third class by a projection vertex, using free stabilizer actions
target: fpbs-mal-two-step-relative-position-rigidity
requires: []
artifacts:
  - research/artifacts/fpbs-iid-chord-union-bound-2026-09-19.md
  - experiments/fpbs-iid-chord-union-bound-2026-09-17/overlap.py
---

Direct proof, artifact §2.

**0. Tree.** Let `T` be the right Cayley tree of `F`, with `F` acting on it
freely by left multiplication. Let `T_K` be the convex hull of `K`, and send
the class `Ky` to `X(Ky) = y^{-1} T_K`.

**1. Stabilizers.** `Stab(T_K)` acts freely and cocompactly on `T_K`, so it
contains `K` with finite index. For `s` in it, `sKs^{-1} ∩ K` is then
nontrivial. Malnormality gives `s in K`. So the classes correspond
bijectively to the translates of `T_K`, and `Stab(X(Ky)) = y^{-1}Ky` acts
freely on vertices.

**2. Overlap (F1).** Distinct translates share at most 3 vertices.
- A common vertex has different core types in the two copies. Equal types
  `v = k r_u = g k' r_u` would force `g in K`.
- So a common subtree immerses into the off-diagonal product of the core
  with itself.
- `overlap.py` finds two components there, each a tree on 3 vertices.
- An immersion of a tree into a finite tree is injective.

Hence every projection `pi_X(Y)` (`X ∩ Y`, or the nearest vertex if they are
disjoint) has at most 3 vertices. It is equivariant under `Stab(X)`.

**3. Transitivity.** The set `{C : D(A, C) = D}` is one free orbit of
`Stab(A)`:
- `K h k y = (K h y)(y^{-1} k y)`, which gives transitivity;
- `C s = C` with `s ≠ 1` would put `s` in two distinct conjugates of `K`,
  which malnormality forbids.

Fix `C_0` in the set `M` of the claim. Every `C in M` has
`X_C = kappa X_{C_0}` with `kappa in Stab(X_A)`, and `X_C = lambda X_{C_0}`
with `lambda in Stab(X_B)`.

**4. Exceptional part.** Let `P = pi_{X_A}(X_B)` and
`Q_C = pi_{X_A}(X_C) = kappa Q_{C_0}`. If `Q_C ∩ P ≠ ∅`, then `kappa` maps
one of the `<= 3` vertices of `Q_{C_0}` to one of the `<= 3` vertices of `P`.
Freeness leaves at most 9 such `kappa`, hence at most 9 such `C`.

**5. Generic part.** Suppose `Q_C ∩ P = ∅`. By convexity:
- `X_C ∖ X_A` lies in components of `T ∖ X_A` attached at `Q_C`;
- `X_B ∖ X_A` lies in components attached at `P`.

So `X_C ∩ X_B = ∅`. The bridge from `X_C` to `X_B` crosses `X_A` and ends at
a vertex `e_C in E = pi_{X_B}(X_A)`, with `|E| <= 3`. For two generic
classes `C_1` and `C`, the element `lambda_C lambda_{C_1}^{-1}` stabilizes
`X_B` and maps `X_{C_1}` to `X_C`, so it carries bridge to bridge and
`e_{C_1} -> e_C`. By freeness, `C` is determined by `e_C`, so there are at
most 3 generic `C`.

**6. Total.** `|M| <= 9 + 3 = 12`. ∎

**Check.** The proof uses only (F1), malnormality and freeness, so the same
argument gives `|M| <= c^2 + c` for any malnormal finitely generated `K` in a
free group whose distinct hull translates share at most `c` vertices.
