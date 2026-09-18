---
rg: 2
id: higman-virtually-solvable-edge-images-collapse
kind: claim
title: In a nontrivial quotient of Higman's group no opposite pair generates a virtually solvable group, so the normal closure of every derived term of <a,c> is all of H4
distinct_from:
  higman-bounded-derived-length-edge-images-collapse: that proves the reduction from derived length k to k - 1 and certifies its nonvanishing input by computer for k <= 11; this proves that input for every k by a Fox-derivation argument, so there is no bound on the derived length.
  solvable-by-metabelian-edge-images-collapse-higman-quotients: that needs finite Hirsch length of the second derived subgroup; this has no rank condition and no derived-length bound.
  nilpotent-edge-images-collapse-higman-quotients: that kills virtually nilpotent and finite-rank virtually solvable images; this kills every virtually solvable image.
artifacts:
  - experiments/higman-magnus-nonvanishing-2026-09-18/witness.py
  - experiments/higman-magnus-nonvanishing-2026-09-18/witness-output.txt
---

**ESTABLISHED** by `higman-virtually-solvable-edge-images-collapse-proof`.

**Statement.** Let `Q` be a quotient of
`H4 = < a, b, c, d | b^a = b^2, c^b = c^2, d^c = d^2, a^d = a^2 >` (`x^y = y^-1 x y`), and let
`F = <a,c>`, which is free in `H4`.

1. **Powers.** If for some `m >= 1` the subgroup `<a^m, c^m>` of `Q` is solvable, then `Q = 1`. The same
   holds for `<b^m, d^m>`.
2. **Normal closures.** `ncl_(H4)(F^(k)) = H4` for every `k >= 1`.
3. **Edge images.** If the image of `<a,c>` or of `<b,d>` in `Q` is virtually solvable, then `Q = 1`.
4. **Trees.** If `Q != 1` acts on a tree without inversions and every edge stabilizer is virtually
   solvable, then `Q` fixes a vertex. So a nontrivial quotient of `H4` never splits as an amalgam or HNN
   extension over virtually solvable subgroups.

**Mechanism.** The route of `higman-bounded-derived-length-edge-images-collapse` reduces derived length
`k` to `k - 1`, given one input (ii): a word `w_0 in F^(k)` whose top tower invariant `S_(k-2)` survives
the substitution `iota_b`. Its Lemmas B and C move nonvanishing across `iota_b` once heights are
shifted up, so (ii) comes down to a statement about the free group `Phi = <alpha, gamma>` alone:
**`S_(k-1)` is not identically zero on `Phi^(k)`.** We prove this for every `k`.

- **Derivation.** On `Phi^(r)` the lower invariants vanish, `pi = S_(r-1)` is a homomorphism to a free
  abelian group `A`, and `delta = S_r` is a Fox derivation over it into a free `Z[A]`-module:
  `delta(uv) = delta(u) + t^(pi u) delta(v)`.
- **Inner forcing.** If `delta` vanished on `[Phi^(r), Phi^(r)] = Phi^(r+1)`, then
  `(1 - t^(pi v)) delta(u) = (1 - t^(pi u)) delta(v)` for all `u, v`. So `delta` would be inner over the
  fraction field: `delta(u) = (1 - t^(pi u)) Z`.
- **Conjugation breaks it.** Conjugating `u` by `x^n`, with `x` the letter of kind `r mod 2`, acts on
  types by an injective relabelling `Theta` and adds `n (1 - t^(pi u)) E`. Innerness then forces
  `z = theta(z) + n` for the coefficient `z` of the fixed basis vector `E`, where `theta` renames
  variables injectively.
- **Field lemma.** That equation has no solution in `Q(t_y)`: `theta` permutes the finite support of
  `z`, so some power fixes `z`, and iterating gives `L n = 0`.
- **Witnesses.** `w_1 = [gamma, alpha]` and `w_(r+1) = [w_r, x_r^n w_r x_r^-n]` have
  `S_(r-1)(w_r) != 0`. `witness.py` checks this exactly for `r <= 6` and `n = 1, 2, 3`.

**What it kills for `higman-group-is-sofic`.** Every glued construction `G_1' *_A G_1'` whose edge image
`A` is virtually solvable is dead, whatever its derived length or rank. An amenable edge image must now
be amenable but not virtually solvable.

**Calibration.** Steps 1–5 of the proof are theorems about the free group, and there they are true:
the lower invariants vanish on each derived term, and the next one does not. The collapse uses the
Higman relations only through the substitution lemmas of the earlier route.
