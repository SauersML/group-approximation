---
rg: 2
id: fp-alternating-full-groups-of-free-subshifts-force-sft-proof
kind: route
title: Nested commutators of rule 3-cycles with shapes chosen in a ball detect every illegal pattern on legal colourings, so relators cut out the subshift
target: fp-alternating-full-groups-of-free-subshifts-force-sft
requires: []
artifacts:
  - research/artifacts/zp-fp-simple-amenable-obstructions-2026-09-13-part2.md
---

## Why sufficient

Full proof in the artifact, Sections 1–4. It needs no minimality and no commutativity of `Λ`.

1. **Lemma 0 (disjointness).** On a colouring whose `B(R_1 + 12)`-windows occur in `X`,
   translates `a·Occ(π)` and `b·Occ(π')` with `a ≠ b ∈ B(6)` are disjoint whenever `π`
   and `π'` agree on `B(R_1)`. A common site would give a point of `X` agreeing with
   its translate by `b^(-1)a ≠ 1` on `B(R_1)`.
2. **Lemma A.** With `[x, y] = x^(-1) y^(-1) x y`, `[[b^(-1), a^(-1)], [b, a]]` acts as the
   3-cycle `a` on `C ∪ aC ∪ a^2 C`, where `C = A_1 ∩ B_1`, whenever `a` and `b` are
   3-cycles whose blocks meet only in `A_1 ∩ B_1`. It is checked directly on the
   five-point model `(p a_1 a_2)`, `(p b_1 b_2)`.
3. **Words.** Climb from `B(r)` to `B(r+1) = B(r) ∪ ⋃_h B(r)h` one generator `h` at a
   time.
   - Intersect occurrences of the partial pattern with those of `q|B(r)h`, whose
     occurrence set is `h^(-1)·Occ(q_h)`.
   - For the second 3-cycle, use a shape in `B(5)` that aligns one block with the
     intersecting block and keeps every other block off the first 3-cycle's blocks.
   - This avoids at most four elements of `B(5)`, which has at least six.
4. **Lemma B.** By induction, each word acts on every legal colouring as the 3-cycle of
   its pattern.
   - An illegal pattern has no occurrences in `X`, so its word is trivial in `Γ`.
   - It still moves a site of any colouring where the pattern occurs.
5. **Relators hold on legal colourings.** Relators and `g^(-1) g` read bounded windows,
   which occur in `X`. By freeness they act trivially, so the rule action factors
   through `Γ`.
6. **Conclusion.** A legal colouring not in `X` carries an illegal pattern whose word is
   `1` in `Γ` but moves a site, which contradicts step 5. So `X` equals the SFT of
   `B(N)`-legal colourings.
