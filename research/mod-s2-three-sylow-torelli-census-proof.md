---
rg: 2
id: mod-s2-three-sylow-torelli-census-proof
kind: route
title: Reidemeister-Schreier for the 3-Sylow preimages inside Pbar = P_5/<Delta^2>, exact unimodular elimination, twist classes up to centralizer orbits, then W, d and A_+ by exact lattice programs
target: mod-s2-three-sylow-torelli-census
requires:
  - genus-two-mapping-class-group-homology-and-symplectic-quotient
  - mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit
  - mod-s2-induced-torelli-characters-have-positive-relation-floors
  - mod-s2-short-generated-torelli-relations-pin-one-thirtieth
artifacts:
  - experiments/mod-s2-three-sylow-census-2026-09-17/sylow.py
  - experiments/mod-s2-three-sylow-census-2026-09-17/pbar.py
  - experiments/mod-s2-three-sylow-census-2026-09-17/fastelim.py
  - experiments/mod-s2-three-sylow-census-2026-09-17/orbits.py
  - experiments/mod-s2-three-sylow-census-2026-09-17/tietze_chain.py
  - experiments/mod-s2-three-sylow-census-2026-09-17/orbits.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/sylow-U.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/pbar-U.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/pbar-U-fast.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/pbar-max0.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/pbar-max1.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/pbar-max2.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/pbar-phi-fast.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/tz-U.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/tz-max0.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/tz-max0-fast.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/exact_d.py
  - experiments/mod-s2-three-sylow-census-2026-09-17/w-U.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/exact-U.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/w-max0.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/exact-max0.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/w-max1.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/exact-max1.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/w-max2.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/exact-max2.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/w-phi.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/exact-phi.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/run-check-phi.log
---

Notation as in the target.

**Inputs.**
- **[HOM]** `genus-two-mapping-class-group-homology-and-symplectic-quotient`, item 4: the exact
  sequence `1 -> K -> M -> Sp_4(Z) -> 1`, so `M -> Sp_4(Z/6)` is onto.
- **Standard facts** (Farb-Margalit, *A primer on mapping class groups*: Chapter 9 for
  Birman-Hilden, §3.6 for capping), cited as in `mod-s2-gamma4-torelli-census-proof`:
  - **(BH)** `M/<iota> = Mod(S_{0,6})`, with `a_i -> sigma_i` and `iota` central, mapping to `-I`;
  - **(CAP)** `B_5/<Delta^2>` is the stabilizer `H` of puncture 6 in `Mod(S_{0,6})`, and
    `P_5/<Delta^2>` is the pure mapping class group `Pbar = PMod(S_{0,6})`.
- **[TA]** `mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit`: the definitions of classes,
  `W` and `d`, and its census row "`Gamma(2)` | 720 | 9 | 10 | 1 | 10 | 1/30". Also, verbatim:
  "(TA2) ... If `Gamma'' <= Gamma'`, then `d(Gamma'') <= d(Gamma')`" and
  "(TA3) ... If `w in W(Gamma')` has `3` not dividing `sum_c w_c`, then `d(Gamma') >= 1/(3 ||w||_1)`".
- **[RF]** `mod-s2-induced-torelli-characters-have-positive-relation-floors`, the definition, verbatim:
  "`A_+(Gamma') = min { chi(b) : b in B, b >= 0, 3 not| chi(b) }`".
- **Presentation.** The machine-checked presentation of the pure braid group `P_5`, the word for
  `Delta^2`, and the separating-twist words `T_A^2` (one for each 3-subset `A` of `{1..5}`). These are
  `pure.py` of `experiments/mod-s2-palindrome-transversal-relations-2026-09-17`, the same inputs as the
  level-four census routes. `pbar.py` re-checks every relator, `Delta^2` and every `T_A^2` against the
  symplectic representation before use.

## Step 1. Reduction to cosets of `Pbar`

1. *`M_V` embeds in `Mod(S_{0,6})`.* `V` is a 3-group, so `-I mod 3` (of order 2) is not in `V`, and
   `-I` is not in `Gamma_V`. So `M_V` meets `<iota>` trivially, and by (BH) it maps isomorphically onto
   its image `Q_V` in `Mod(S_{0,6})`. Hence `H_1(M_V) = H_1(Q_V)`.
2. *`Q_V <= Pbar` has index `[Gamma(2) : Gamma_V]/2`.*
   - Every standard generator `A_ij` of `P_5` is a conjugate of `sigma_1^2`. Its symplectic image is the
     square of a transvection, so it is `I mod 2`. So `Pbar` lies in the kernel of
     `Mod(S_{0,6}) -> Sp_4(F_2)`.
   - Both groups have index 720 = `|S_6|` = `|Sp_4(F_2)|` (the map is onto by [HOM]), so they are equal.
   - Hence `Q_V` is the preimage in `Pbar` of `+-Gamma_V / Gamma(6)` under `Pbar -> Gamma(2)/{+-I}Gamma(6)`,
     and `[Pbar : Q_V] = [Gamma(2) : Gamma_V]/2`. This is the "cosets" column: 320, 960, 2880.
3. *Every separating twist is a `Pbar`-conjugate of one of the ten `T_A^2`.*
   - By Step 1.3 of `mod-s2-gamma4-torelli-census-proof` (which uses only (BH), (CAP) and change of
     coordinates), every separating twist maps to `b (sigma_1 sigma_2)^6 b^(-1)` with `b` in `H`.
   - `B_5 = union_A P_5 gamma_A <sigma_1, sigma_2, sigma_4>`, with `A` running over the ten 3-subsets
     and `gamma_A` the braids of `pure.py`. Indeed `<sigma_1, sigma_2, sigma_4>` maps onto
     `Stab{1,2,3} = S_3 x S_2` in `S_5`.
   - So `b = p gamma_A s`. Here `s` commutes with `(sigma_1 sigma_2)^3`, which is central in
     `<sigma_1, sigma_2>` and disjoint from `sigma_4`.
   - Therefore `b (sigma_1 sigma_2)^6 b^(-1) = p T_A^2 p^(-1)`, where `T_A = gamma_A (sigma_1 sigma_2)^3
     gamma_A^(-1)`. `pure.py` (`standard_twists`) asserts this identity in `Aut(F_5)`.
4. Conversely, each `p T_A^2 p^(-1)` is a separating twist in the Torelli image, which is normal. Its
   class in `H_1(Q_V)` depends only on the coset `Q_V p`. So the set of classes `v_c` equals
   `{ [p T_A^2 p^(-1)] : Q_V p in Q_V \ Pbar, A }`. By [TA], `W`, `d` and `A_+` depend only on this set of
   distinct classes.
5. *Centralizer orbits.* Let `h` in `P_5` commute with `T_A^2`. `pbar.py` (`centralizer_words`) checks
   this in `Aut(F_5)`, which is faithful (Artin). Then the cosets `Q_V p` and `Q_V p h` give the same
   class. So one representative per orbit of `<centralizer words>` on the cosets suffices. This is the
   `--fast` mode. The centralizer sizes used are the 4 or 5 words per `A` printed in the logs.

## Step 2. Exact computation of `H_1(Q_V)` and the classes (`pbar.py`, `fastelim.py`, `sylow.py`)

1. The right action of the `A_ij` on `Q_V \ Pbar` is computed on the keys
   `min over u in +-V of (u X mod 3)` of the symplectic images `X` mod 6. The script checks that every
   relator and `Delta^2` act trivially.
2. Abelianised Reidemeister-Schreier gives integer relators on the Schreier generators, and the twist
   words are rewritten into Schreier vectors. For `Phi` there are 25921 generators and 103680 relators.
3. *Exact elimination.* A generator with coefficient `+-1` in a relator is solved for and substituted
   into every relator and every twist vector. This is a unimodular change of variables, so it
   preserves the abelian group and the images of the twists exactly. `fastelim.py` only chooses the
   pivot order (Markowitz); the arithmetic is exact Python integers.
4. The remaining relators are put in HNF, and `h1_invariants` (Smith form) gives `H_1`. Twist vectors
   are reduced modulo the HNF (`reduce_mod_hnf`). This gives canonical representatives of
   `Z^n / rowspace`, so two twists have the same class iff the reduced vectors are equal. `W` is the
   HNF of `[relators | 0 ; classes | I]` restricted to rows with zero left block (`w_lattice`).

## Step 3. Cross-checks and conjugacy

1. At `V = U`, three independent pipelines agree on `H_1`, the number of classes and `rank W`:
   - the `B_5` model with 38400 cosets of `H` (`sylow.py`, `sylow-U.json`);
   - the `Pbar` model, full and `--fast` (`pbar-U.json`, `pbar-U-fast.json`);
   - the two-stage Tietze pipeline (`tz-U.json`).
   At `max_0`, the full, fast and Tietze runs agree (`pbar-max0.json`, `tz-max0.json`, `tz-max0-fast.json`).
2. *Conjugate `V` give the same row.* `Sp_4(Z) -> Sp_4(Z/2) x Sp_4(F_3)` is onto ([HOM] and CRT), and
   `Gamma(2)` is normal. So `V' = g V g^(-1)` in `Sp_4(F_3)` gives `Gamma_V' = g~ Gamma_V g~^(-1)` for a lift `g~`,
   and `M_V'`, `M_V` are conjugate in `M`. Conjugation carries separating twists to separating twists,
   so it preserves `H_1`, the classes, `W`, `d` and `A_+`. `orbits.py` gives the classes of maximal
   subgroups `[0, 1, 2, 2]` (so `max_2 ~ max_3`), and for the order-3 subgroups of `Phi` it gives
   `[0, 1, 1, 1]`.

## Step 4. The bounds, in exact arithmetic

Let `B` be the HNF basis of `W` (`r` rows, `m` classes), `a_i = aug(B_i)`. Lift `W^perp` to
`{h in R^m : B h in Z^r}` (TA's definition), and write `h = (1/3) 1 + e`. Then `d = min ||e||_inf`.

1. *`d <= 1/30`.* `gcd aug W = 10`, computed exactly from `B`. So `theta = (3/10) 1` has
   `B theta = (3/10) a in Z^r`, and `||theta - (1/3) 1||_inf = 1/30`. (This also follows from (TA2) and
   `d(Gamma(2)) = 1/30`.)
2. *`d >= 1/30`, primary proof (short generation).* Replace `B` by an LLL basis `R`. `exact_d.py` checks
   that the HNF of `R` equals the HNF of `B`, so `R` is a basis of `W` in class coordinates.
   - It records the set of row types `(|aug|, l1)` (`basis_row_types_abs_aug_l1` in `exact-<V>.json`).
     For `V = U, max_0, max_1, max_2` every type is `(0, l)` with `l <= 16` or `(10, l)` with `l <= 18`
     (table, column "SG"). So (SG) of `mod-s2-short-generated-torelli-relations-pin-one-thirtieth` holds
     (flags `short_generated` and `short_generated_general`).
   - For `V = Phi` (`run-check-phi.log`, from `exact_d.py --check w-phi.json`), `R` has a row of type
     `(10, 22)`, so the flags are false. The split test (`sg_split` in `exact-phi.json`) gives:
     - `w_1 in W` with `aug(w_1) = 10` and `||w_1||_1 = 16`;
     - an LLL basis of `W_0 = W cap ker aug` with every `l1 <= 24`;
     - an exact check that `HNF(W_0 basis + w_1) = HNF(B)`.

     This generating set satisfies (SG).
   - By that claim (its Step 4.1 passes from class coordinates to `X`), `d(Gamma_V) = 1/30`.
3. *`d >= 1/30`, independent check (box certificate, `exact_d.py`).*
   - This uses the same `R`.
   - Suppose `||e||_inf <= 1/30`. Then `k = R h` is an integer vector with
     `|k_i - a_i/3| = |R_i e| <= ||R_i||_1 / 30`, so `k` lies in an explicit finite box.
   - For each `k` in the box and every `y in Q^r`, `R e = k - a/3` implies
     `|y.(k - a/3)| = |(R^T y).e| <= ||R^T y||_1 ||e||_inf`.
   - A float LP proposes `y`. It is rounded to a rational vector, and the bound is evaluated with
     Fractions. The run records the box size and the least exact bound over the box.
   - Controls on `U`: target `1/29` fails, with LP value `1/30` and the exact bound `1/30` on the only
     box point, while target `1/31` succeeds.
   - Results are in `exact-<V>.json`, and every certified `V` has least bound exactly `1/30`. Since
     `Phi <= V`, (TA2) then gives `d = 1/30` on the whole interval `Gamma_Phi <= Gamma' <= Gamma(2)`.
4. *`||w||_1 = 12`, `aug(w) = 10`.* `census.best_certificate` returns `w = B^T y` with integer `y`, so
   `w in W` exactly. Its minimality is only the MILP's claim.
5. *`A_+ <= 20`.* `sylow.positive_certificate` returns `w = B^T y` and asserts `min w >= 0` and
   `aug(w) = 20` (with `3` not dividing 20). Minimality, that is excluding `aug = 10`, is only the MILP's
   claim. `exact_d.py` also searches, by MILP, for a `theta in W^perp` with all `0 < theta_c < 1/10`. Such a
   `theta` would exclude mass 10, and it would be checked exactly. The search finds none at `U`.
