---
rg: 2
id: sl3-zp-torsion-free-index-48-proof
kind: route
title: S_4 acts freely on cosets; Sylow 2-subgroups for odd p; an exhaustive mod-16 search at p = 2
target: sl3-zp-torsion-free-open-subgroups-have-index-divisible-by-48
requires: []
---

Let `W <= SL_3(Z_p)` be torsion-free and open, and put `n = [SL_3(Z_p) : W]`.

**(a) 24 divides n.** Let `F` be a finite subgroup of `SL_3(Z_p)`. The stabilizer
in `F` of a coset `gW` is `F cap gWg^(-1)`. That is a finite subgroup of a
torsion-free group, so it is trivial. So `F` acts freely on `SL_3(Z_p)/W`, and
`|F|` divides `n`. Take `F = S_4`, the signed permutation matrices of
determinant 1.

**(b) p odd: 16 divides n.**
- `|SL_3(F_p)| = p^3 (p^2 - 1)(p^3 - 1)`. Here `p^3 - 1 = (p - 1)(p^2 + p + 1)`
  and the second factor is odd.
- So `v_2 = v_2(p^2 - 1) + v_2(p - 1) >= 3 + 1 = 4`.
- The kernel of reduction mod `p` is pro-`p`, so a Sylow 2-subgroup lifts to a
  finite subgroup of `SL_3(Z_p)` (profinite Schur--Zassenhaus).
- By (a), 16 divides `n`.

**(c) p = 2: 16 divides n.** Suppose `v_2(n) = 3`, the least value (a) allows.
- **The image is a 2-group.** The image of `W` in `SL_3(F_2)`, of order
  `168 = 2^3 * 3 * 7`, has no element of order `q` in `{3, 7}`. Otherwise
  choose `w in W` mapping to one. The closure of `<w>` is procyclic, and its
  pro-`q` part is nontrivial. That part is finite, since it meets the pro-2
  kernel `K_1` trivially. So `W` would contain an element of order `q`.
- **Reduction to the Iwahori.** The image is therefore a 2-group. After
  conjugation, `W <= I`, the preimage of the unitriangular group, and
  `n = 21 [I : W]`. So `[I : W] = 8`.
- **Level.** Every index-8 subgroup of `I` contains
  `K_4 = ker(SL_3(Z_2) -> SL_3(Z/16))`. Put `K = W cap K_1`, of index at most 8
  in `K_1`. A chain of index-2 steps down to `K` passes through
  `Phi(K_1) = K_2` (`sl_3(F_2)` is perfect), then `K_2^2 = K_3`, then
  `K_3^2 = K_4` (`K_2` is uniform). `Phi` is monotone. See the artifact,
  Section 4.
- **Forbidden set.** `W <= I` is pro-2, so it is torsion-free exactly when it
  contains no involution.
  - Over `Z_2`, a rank-3 involution of determinant 1 is `diag(1,-1,-1)` or
    `[[0,1],[1,0]] (+) (-1)`. The indecomposable `Z_2[C_2]`-lattices are the
    trivial, sign and regular lattices.
  - Neither `GL_3(Z_2)`-class splits in `SL_3(Z_2)`, since each centralizer
    contains elements of every determinant.
  - Reduction `SL_3(Z_2) -> SL_3(Z/16)` is surjective. So the images of all
    involutions form the union of the two `SL_3(Z/16)`-classes: sizes 7168 and
    86016, of which 27648 lie in `I/K_4`.
- **Search** (`experiments/strong-atiyah-sl3z/iwahori_index8_search.g`, MSI
  sbatch 556104, log in `iwahori_index8_search.out`, about 3 minutes). The script:
  - builds `I/K_4` as a matrix group mod 16 and checks its order is `2^27`;
  - converts it to a pc group;
  - enumerates every chain `P > M1 > M2 > W` of index-2 subgroups, 7 choices of
    `M1` and 69 of `M2`;
  - decides the last step exactly. `W = ker(chi)` for a nonzero character `chi`
    of `M2/Phi(M2)`. It avoids the forbidden set if and only if no forbidden
    element lies in `Phi(M2)` and `chi(t) = 1` for every forbidden `t in M2`,
    a linear system over `F_2`.
  Every index-8 subgroup of a finite 2-group arises this way. The search printed
  `RESULT: no torsion-free index-8 subgroup of I exists`.

  Two lines of the log need a word.
  - `Frattini rank of P: 27` counts the pc generators of the quotient group, not
    its rank. The 7 maximal subgroups show the rank is 3.
  - The `Syntax warning: Unbound global variable` lines are GAP's parse-time
    notices for `F`, `hom` and `pcg`. These are assigned inside the loop before
    the closures that use them run.

So `v_2(n) >= 4`. Together with (a), 48 divides `n`.
