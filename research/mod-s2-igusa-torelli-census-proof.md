---
rg: 2
id: mod-s2-igusa-torelli-census-proof
kind: route
title: Lift the 512-coset level-four Fox complex to a free Z[F_2^4]-complex for the Igusa preimage, eliminate over the local ring (Z/2^8)[F_2^4], read the 2-primary homology and the twist classes, and recompute W, d and A_+
target: mod-s2-igusa-torelli-census-is-one-thirtieth
requires:
  - mod-s2-two-adic-torelli-tower-keeps-rank-to-level-sixteen
  - mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit
  - mod-s2-induced-torelli-characters-have-positive-relation-floors
  - mod-s2-gamma4-torelli-census-is-one-thirtieth
artifacts:
  - experiments/mod-s2-igusa-torsion-2026-09-17/za_igusa.py
  - experiments/mod-s2-igusa-torsion-2026-09-17/igusa_exact.py
  - experiments/mod-s2-igusa-torsion-2026-09-17/w_compare.py
  - experiments/mod-s2-igusa-torsion-2026-09-17/igusa-census-results.json
---

Notation as in the target.

**Inputs.**
- **[T]** `mod-s2-two-adic-torelli-tower-keeps-rank-to-level-sixteen`, item (I48), verbatim:
  "`H_1(pi^(-1) Gamma(4,8)) = Z^54 (+) Z/2^k` with `1 <= k <= 4`", with "so there is no odd torsion, and
  the torsion is cyclic". Its proof (`mod-s2-two-adic-torelli-tower-rank-proof`, Step 3) supplies the
  presentation used here: "the twisted Fox matrix of the 512-coset presentation of `K4` inside
  `Pbar = P_5/<Delta^2>` (`pure.py`, `palindrome.py`)".
- **[TA]** `mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit`: the definitions of classes,
  `W` and `d`. Also "(TA2) ... If `Gamma'' <= Gamma'`, then `d(Gamma'') <= d(Gamma')`", and
  "(TA3) ... If `w in W(Gamma')` has `3` not dividing `sum_c w_c`, then `d(Gamma') >= 1/(3 ||w||_1)`".
- **[RF]** `mod-s2-induced-torelli-characters-have-positive-relation-floors`: the definition of `A_+`.
- **[G4]** `mod-s2-gamma4-torelli-census-is-one-thirtieth`: at `Gamma(4)` there are 160 classes, `W` has
  rank 106 and is saturated, and `d = 1/30`.

## Step 1. Equivariant chains (`za_igusa.py build_rows`)

- `level4_cosets` enumerates the 512 cosets of `K4 = pi^(-1) Gamma(4)` in `Pbar` and keeps each
  representative matrix mod 8. It asserts agreement with `between48.enumerate_cosets`.
- `gen_labels` assigns each Schreier generator `(c, p)` the element of
  `A = Gamma(4)/Gamma(4,8) = sp_4(F_2)/Alt = F_2^4` given by `Y = rep_c mat_p rep_d^(-1)`, `X = (Y - I)/4`.
  - The matrix of an element of `Pbar` is defined only up to the central sign `-I` (the hyperelliptic
    involution). Since `-I` is not in `Gamma(4)`, exactly one sign of `Y` is `= I mod 4`, and that sign
    is used.
  - It asserts `Y = I mod 4` and label 0 on tree edges.
- The 16-sheeted cover of the level-four presentation complex is a presentation complex of `G_I`. Its
  chains are `Z[A]^18432 -> Z[A]^4609 -> Z[A]`, where 18432 counts relators times cosets and 4609 counts
  Schreier generators. The first map is the Fox matrix, traced letter by letter with the running
  `A`-value (`ztrace`).
- The code asserts two closure facts:
  - every relator closes in the `A`-cover, which confirms that the labels define `K4 -> A`;
  - every twist-square lift closes, so the separating twists lie in `G_I`.
- All 16 labels occur. So `K4 -> A` is onto, and the cover is connected with 8192 cosets.
- Put `Q = C_1 / im d_2`. Then `im d_1` is the augmentation ideal of `Z[A]`, which is free of rank 15.
  So `Q = H_1(G_I) (+) Z^15`.

## Step 2. Local-ring elimination (`build_mod`, `m_eliminate`, `dense_eliminate`)

- `R = (Z/2^8)[A]` is local, because `A` is a 2-group. Its units are exactly the elements of odd
  augmentation. The inverse is computed by Newton iteration, and `rinv` asserts `u y = 1`.
- Pivoting a relator row on a unit entry is an invertible row/column operation over `R`. So
  `Q (x) Z/2^8`, and the images of the twist vectors in it, are preserved when the same operations are
  applied to those vectors.
- The sparse phase uses 4354 pivots on `+-a`. The dense phase then pivots on any unit: 201 further
  pivots, in float32 arrays that stay exact since `16 * 2^16 < 2^24`, as asserted.
- The phases stop when no unit entry is left. This leaves 54 `R`-columns and 13539 rows.
- The count 54 is forced. By Nakayama it equals `dim Q (x)_R F_2`. The level-four complex has one
  vertex, so `Q (x)_(Z[A]) Z = H_1(K4) = Z^54`, and hence `Q (x)_R F_2 = H_1(K4; F_2)`.

## Step 3. Smith form and homology (`census_mod`)

- The surviving rows, expanded over `A`, give an 864-column matrix over `Z/2^8`.
- Random 0/1 row mixes, exact in float64, are brought to Smith form (`smith_mod`). The code then
  asserts that every one of the 216624 expanded relator rows lies in the module found. So the mixing
  lost nothing, and the result is the Smith form of `Q (x) Z/2^8`.
- The result is `Q (x) Z/2^8 = (Z/2^8)^69 (+) Z/2`, with no other torsion. By [T], `Q = Z^69 (+) Z/2^k`
  with `k <= 4 < 8`. Hence `k = 1`, and (H) follows.

## Step 4. Classes and relations

- The class of a separating twist of `G_I` is `b . z` for `b in A`, where `z` is the traced lift of a
  twist square at a level-four coset.
- Its key is:
  - the level-four class, i.e. the image under `i : H_1(G_I) -> H_1(K4) = Z^54` (`igusa_exact.py level4`);
  - its Smith coordinates in `Q (x) Z/2^8`, those with a nonzero modulus.
- This key map is a homomorphism on `H_1(G_I)`, and it is injective:
  - `b_1(G_I) = 54 = b_1(K4)` by [T], so `ker i` is finite, hence inside the torsion `Z/2`;
  - the torsion `Z/2`, a direct summand of `Q`, embeds in `Q (x) Z/2^8`.
- So equal keys means equal classes. There are 160 classes, one over each level-four class, which
  gives (C). The torsion coordinate `eps` equals 1 on 76 of them.
- `W(Gamma(4,8))` is the kernel of `Z^160 -> H_1(K4) (+) (+)_t Z/2^(v_t)`, computed by `census.w_lattice`.
- Pushing forward along `i`, and using fibres of size one, gives `W(Gamma(4,8)) <= W(Gamma(4))`.
- `w_compare.py` finds equal rank (106) and equal Gram determinant. So the two lattices are equal,
  which gives (W). It also checks `eps . w = 0 mod 2` on a basis of `W(Gamma(4))`, consistently.

## Step 5. Census (`milp`)

- `census.distance_milp` on `W` gives `d = 1/30`, with the constant character `3/10`.
- `census.best_certificate` gives a 0/1 relation of mass 10, one class over each level-two splitting.
  By (TA3), `d >= 1/30`.
- `between48.positive_min` gives minimum 10 for augmentation `1 mod 3` and 20 for `2 mod 3`. The gcd of
  augmentations is 10, so `A_+ = 10`.
- These are the numbers of [G4]. That is forced by (W), and it re-checks the MILP layer.
- All outputs are in `igusa-census-results.json`.

## Reproduction

```text
python3 igusa_exact.py level4 level4.pkl
python3 za_igusa.py build_mod zam.pkl          # ~11 min on 4 cores
python3 za_igusa.py census_mod zam.pkl level4.pkl res.json
python3 za_igusa.py milp res.json final.json
python3 w_compare.py level4.pkl res.json.pkl
```
