---
rg: 2
id: mod-s2-two-adic-torelli-tower-rank-proof
kind: route
title: Transfer lemma plus Shapiro decomposition of the 2-adic covers of M_4 over characters of Gamma(4)/Gamma(8) (exact over Z) and Gamma(4)/Gamma(16) (modulo p and modulo the inert prime 3 of Z[i])
target: mod-s2-two-adic-torelli-tower-keeps-rank-to-level-sixteen
requires:
  - mod-s2-gamma4-torelli-census-is-one-thirtieth
  - mod-s2-induced-torelli-characters-have-positive-relation-floors
  - genus-two-mapping-class-group-homology-and-symplectic-quotient
artifacts:
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/pure.py
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/palindrome.py
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/between48.py
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/groupring.py
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/characters.py
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/level8_betti.py
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/level8-betti-results.json
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/level16_betti.py
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/level16-betti-results.json
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/level16_f9.py
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/level16-f9-results.json
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/random1-results.json
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/igusa48-results.json
---

Notation as in the target. All paths below are relative to
`experiments/mod-s2-palindrome-transversal-relations-2026-09-17/`.

**Inputs.**
- **[G4]** `mod-s2-gamma4-torelli-census-is-one-thirtieth`, (G1)-(G3):
  - `H_1(M_4) = Z^54` is torsion-free;
  - there are 160 classes `v_c`;
  - `W` has rank 106 and augmentation gcd 10;
  - its Step 1 Birman-Hilden reduction gives `M_4 = K4`, with `-I` not in `Gamma(4)`.
- **[PF]** `mod-s2-induced-torelli-characters-have-positive-relation-floors`: the definitions of `B`,
  `A_+` and (RF).
- **[HOM]** `genus-two-mapping-class-group-homology-and-symplectic-quotient`: `pi` is onto, and `I = ker pi`.
  So `M_4 / M_N = Gamma(4)/Gamma(N)`, and `I <= M_N` for every `N`.

## Step 1. The transfer lemma (R)

Let `Lambda'' = Lambda(Gamma'') <= Lambda' = Lambda(Gamma')`, of index `n`. The transfer
`tr : H_1(Lambda') -> H_1(Lambda'')` satisfies `i o tr = n`, so `i (x) Q` is onto. If the ranks
agree, `i (x) Q` is an isomorphism. Then `ker i` is torsion and finitely generated, hence finite, and
`Hom(H_1(Lambda''), R) = i^* Hom(H_1(Lambda'), R)`. That is (b).

For (a), take a positive relation at `Gamma'`: a word `w = t_(s_1)^(n_1) ... t_(s_k)^(n_k)`,
`n_j >= 1`, `3 not| sum n_j`, with `[w] = 0` in `H_1(Lambda')`.
- Every `t_s` lies in `I <= Lambda''`, so `[w] in H_1(Lambda'')` is defined and lies in `ker i`.
- Hence `[w^e] = e [w] = 0`. Its vector in `H_1(I)_(Gamma'')` is nonnegative with coordinate sum `e sum n_j`, which is prime to 3.

For (c), `ker i` is torsion inside a torsion-free group, so it is zero. The class map of separating
twists at `Gamma''` is then carried injectively onto the class map at `Gamma'`, since these are the
same twists. So the relation modules on classes coincide.

## Step 2. (A4)

`characters.py` (function `positive_min`, run in `random1-results.json`) solves the integer program
`min chi(b)` over `b >= 0` in `W`, with `chi(b) = 1` or `2 mod 3`, on the 160 classes. The index-2
cover used there has torsion-free `H_1 = Z^54` (`h1_F2_dim = h1_rank = 54`, no odd torsion in the
sign component). So by Step 1(c) its classes and `W` are those of `Gamma(4)`:
- the minimum is 10, supported on 10 classes, one over each level-two splitting, each with
  multiplicity 1;
- the minimum with augmentation `2 mod 3` is 20.

Since `gcd = 10`, `A_+(Gamma(4)) = 10`.

## Step 3. Shapiro over an abelian quotient

Let `A = M_4 / M_N` be abelian (`N = 8, 16`). Then `H_1(M_N; R) = H_1(M_4; R[A])` for every
coefficient ring `R`. If `|A|` is a unit in `R` and `R` contains the values of the characters of `A`, then
`R[A] = (+)_f R_f`, and so `H_1(M_N; R) = (+)_f H_1(M_4; R_f)`.

`H_1(M_4; R_f)` is computed from the twisted Fox matrix of the 512-coset presentation of `K4` inside
`Pbar = P_5/<Delta^2>` (`pure.py`, `palindrome.py`). The Schreier generator images in `A` are computed
from the symplectic matrices of the pure braids (`between48.py`), and every relator is checked to close in the
`A`-cover (assertion in `relator_terms`). For `f != 0` the Fox cokernel is `H_1(K4, *; R_f)`. It
contains `H_1(K4; R_f)` with quotient `(f(A) - 1)`-ideal in `R`, which is free of rank one when `R` is a domain. So
`rank coker = b_1^f + 1`, and the torsion of the cokernel is the torsion of `H_1(K4; R_f)`.

`Mod(S_2)` conjugation permutes the characters: `Sp_4` acts on `sp_4(F_2)` by `X -> g X g^(-1)`, and
on `Sym_4(Z/4)` by `Y -> g^(-T) Y g^(-1)` with `Y = J X`. It preserves the twisted homology, so one
representative per orbit suffices.
- At `N = 8` there are 15 orbits of nontrivial characters, of sizes 15, 60, 20, 45, 180, 180, 60, 15, 60,
  90, 120, 90, 72, 10 and 6. The sizes sum to 1023.
- At `N = 16` there are 157 nontrivial orbits: 15 of order 2 (these are the level-8 characters) and 142 of order 4.

## Step 4. (B8), exact over Z

`level8_betti.py` computes the Smith normal form of each order-2 twisted Fox matrix over `Z`
(`R_f = Z` with `A` acting by `+-1`). Every orbit gives cokernel `Z (+) (Z/2)^53`, except orbit 3
(size 45), which gives `Z (+) (Z/2)^52 (+) Z/4`. So:
- `b_1^f = 0` for all `f != 0`;
- `H_1(M_4; Z_f)` is a 2-group of exponent at most 4;
- there is no odd torsion, so over `Z[1/2]` the splitting gives
  `H_1(M_8)[1/2] = H_1(M_4)[1/2]`.

Hence `b_1(M_8) = 54`, and `H_1(M_8)` has no odd torsion.

Exponent bound. Over `Z`, `0 -> Z[A] -> (+)_f Z_f -> Q -> 0` with `|A| Q = 0`, because
`|A| e_f in Z[A]`. The long exact sequence gives
`H_2(M_4; Q) -> H_1(M_8) -> (+)_f H_1(M_4; Z_f)`. The first map has image killed by `|A| = 2^10`.
Take `x in ker i`. Its trivial component is `i(x) = 0`.

The other components are killed by 2. For each `f`, the composite
`H_1(M_8) -> H_1(M_4; Z_f) -> H_1(M_4; F_2)` is induced by `Z[A] -> Z_f -> F_2`. Since `f` is
`+-1`-valued, this is the augmentation mod 2. So the composite equals
`H_1(M_8) -> H_1(M_4) -> H_1(M_4; F_2)`, and it kills `x`. By universal coefficients,
`H_1(M_4; Z_f) (x) F_2` injects into `H_1(M_4; F_2)`, so `x_f` lies in `2 H_1(M_4; Z_f)`.
- That group is `0` when `H_1(M_4; Z_f) = (Z/2)^53`, which holds for 14 of the 15 orbits.
- It is `Z/2` when `H_1(M_4; Z_f) = (Z/2)^52 (+) Z/4`, which holds for orbit 3.

Hence `2x` maps to zero in `(+)_f H_1(M_4; Z_f)`. So `2x` lies in the image of `H_2(M_4; Q)`, and
`2^11 x = 0`. By Step 1(a) and (A4), `A_+(Gamma(8)) <= 2^11 * 10 = 20480`.

## Step 5. (B16), modulo p and modulo 3

`level16_betti.py` reduces each order-4 or order-2 twisted Fox matrix over `Z[i]` modulo the prime
`p = 998244353` (`p = 1 mod 4`, so `i` has an image in `F_p`) and computes its rank by sparse elimination.
Since `rank_(F_p) <= rank_(Q(i))`, `dim coker_(F_p) >= b_1^f + 1`. Every nontrivial orbit gives
`dim coker = 1`, so `b_1^f = 0`. The trivial orbit gives 54. Hence
`b_1(M_16) = 54 + sum_f |orbit| * 0 = 54`, and the same holds for every `Gamma'` in between, because its
characters are a subset.

`level16_f9.py` repeats this over `F_9 = Z[i]/(3)`. Here `3` is inert, and `|A| = 4^10` is a unit in `Z_(3)`,
so the splitting holds over `R = Z_(3)[i]`, a discrete valuation ring with residue field `F_9`. Every
nontrivial orbit gives `dim_(F_9) coker = 1`. So `H_1(M_4; Z_(3)[i]_f) (x) F_9 = 0`, and by Nakayama
`H_1(M_4; Z_(3)[i]_f) = 0`. Therefore `ker(H_1(Lambda(Gamma')) -> H_1(M_4)) (x) Z_(3) = 0` for every
`Gamma(16) <= Gamma' <= Gamma(4)`: it is finite (Step 1) of order prime to 3. Step 1(a) with (A4)
gives `A_+(Gamma') < infinity`, and Step 1(b) gives the statement about real characters.

## Step 6. Codim-one check

`characters.py` on the random hyperplane (seed 1) finds:
- `h1_rank = h1_F2_dim = 54`;
- sign-component cokernel `Z (+) (Z/2)^53`, so no odd torsion.

Hence `H_1 = Z^54` is torsion-free (`dim H_1(-; F_2) = rank` and no odd torsion), and Step 1(c)
applies. The recomputed census (160 classes, `W` of rank 106, gcd 10, `d = 1/30`) agrees.

## Step 7. (I48)

`characters.py igusa48` (with `CHAR_RANKS_ONLY=1`, output `igusa48-results.json`) works on the
16-sheeted cover `G = pi^(-1) Gamma(4,8)` of `M_4`, which has 8192 cosets in `Pbar`.
- *F_2 dimension.* `f2_dimension` eliminates over the local ring `F_2[A]`. It gives
  `dim H_1(Y, Y^0; F_2) = 55 + 15`, so `dim H_1(G; F_2) = 55`.
- *Character components.* The 16 components have cokernels `Z^54` (trivial `chi`) and
  `Z (+) (Z/2)^53` (each of the 15 nontrivial `chi`). So `b_1(G) = 54` and there is no odd torsion.
- *Torsion.* Hence `tors H_1(G)` is a 2-group with `55 - 54 = 1` cyclic factor, that is `Z/2^k`
  with `k >= 1`.
- *Bound on k.* It lies in `ker i`. As in Step 4, its `chi`-components lie in
  `2 (Z/2)^53 = 0`, and `|A| = 16`, so `k <= 4`.
- *A_+.* Step 1(a) gives `A_+(Gamma(4,8)) <= 2^k * 10 <= 160`. Every relation at `Gamma(4,8)` maps
  to one at `Gamma(4)`, where the augmentation gcd is 10. So the value lies in
  `{10, 20, 40, 80, 160}`.

The same `f2_dimension` gives `dim = rank = 54` on the codim-one cover of Step 6, which is a
consistency check of the method.
