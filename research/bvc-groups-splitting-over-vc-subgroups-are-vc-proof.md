---
rg: 2
id: bvc-groups-splitting-over-vc-subgroups-are-vc-proof
kind: route
title: Rigid length-two products, counting modulo a normal cyclic subgroup, and virtual solvability
target: bvc-groups-splitting-over-vc-subgroups-are-vc
requires:
  - bvc-amalgams-have-two-transitive-vertex-actions
  - non-ascending-hnn-extensions-lack-bvc
  - virtually-solvable-bvc-groups-are-virtually-cyclic
artifacts:
  - research/artifacts/bvc-vc-splittings-2026-09-16.md
---

The full proof is in `research/artifacts/bvc-vc-splittings-2026-09-16.md`, §0–§4. The other
inputs are the normal form and conjugacy theorems for amalgams (Lyndon–Schupp Ch. IV §2, with
IV.2.8 in the form used by `bvc-amalgams-have-two-transitive-vertex-actions-proof`) and
elementary facts about virtually cyclic groups, proved in §0.

**Property P** means that every element is conjugate into one of finitely many virtually cyclic
subgroups. BVC implies P, and P passes to quotients.

**Amalgam `G = A *_C B`, `C` VC.**

1. *Class bound (Lemma 1).* Under P, for each `l >= 2` the elements whose cyclically reduced
   length is `l` lie in at most `K` conjugacy classes. This is Step 3 of the landed amalgam route
   with P in place of BVC.
2. *Rigidity (Lemma 2).* If `ab ~ ab'` with `a` in `A - C` and `b, b'` in `B - C`, then
   `b' = (a^{-1}ca) b c^{-1}` for some `c` in `D_a = C ∩ aCa^{-1}`. With Lemma 1,
   `|B - C| <= K |D_a|`, so a finite `D_a` makes `B` finite (Proposition 3).
3. *Finite index.* `bvc-amalgams-have-two-transitive-vertex-actions` gives
   `[A:C] = 1 + [C:D_a]`. If this is infinite and `C` is infinite, `D_a` is finite, so `B` and
   then `C` are finite, a contradiction. So `A` and `B` are VC.
4. *Index two.* If `C` is infinite, `Z = <z^{R_A R_B}>` for `z` in `C` of infinite order is
   normal in `G`. The quotient `(A/Z) *_{C/Z} (B/Z)` has finite factors and property P. It has at
   least `((p-1)(q-1))^m / m` classes of length `2m` (Lemma 4), which Lemma 1 bounds uniformly.
   So `p = q = 2`.
5. *Conclusion.* `C` is normal and `G/C ≅ D_∞`. If `C` is infinite, `G` is virtually solvable
   (characteristic cyclic `K <= C`, then Lemma 0) and not VC, which contradicts
   `virtually-solvable-bvc-groups-are-virtually-cyclic`. So `C` is finite and `G` is VC.

**HNN extension over VC `C`.**

1. `non-ascending-hnn-extensions-lack-bvc` gives `C = H` (after inverting `t`), so `H` is VC.
2. The kernel of `G -> Z` is `N = ∪ t^{-k} H t^k`.
3. If `H` is finite, `G = H ⋊ Z` is VC.
4. If `H` is infinite, `G` is not VC. The maximal finite normal subgroups of the copies of `H`
   coincide, giving a finite `L` normal in `G`. `G/L` is solvable: the elements of infinite order
   in `N/L`, together with 1, form an abelian normal subgroup of index at most 2 in `N/L`. So `G`
   is virtually solvable, which contradicts `virtually-solvable-bvc-groups-are-virtually-cyclic`.
