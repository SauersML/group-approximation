---
rg: 2
id: thompson-v-single-relator-quotients-have-no-small-images
kind: claim
title: The one-relator quotients G0/<<r5>> and G0/<<r8>> of S4 amalgamated with S3 are perfect and have no nontrivial image in PGL(2,F) for any field F, no nontrivial action on at most 16 points, and no simple quotient among the small simple groups; relator families inside {r6,r7} die at the sign character
distinct_from:
  thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3: that identifies V as the quotient of G0 by all four words r5..r8; this studies the quotients of G0 by single words and subfamilies, which surject onto V and could a priori be much larger.
  thompson-v-mf-iff-opnorm-s4-s3-defect-gap-vanishes: that reduces V not MF to a uniform operator-norm defect gap for the four-relator family; this shows which subfamilies can carry such a gap at all (every one containing r5 or r8 survives every exact finite and rank-2 test; every one inside {r6, r7} is killed by the sign character), and so offers the one-relator strengthenings Gap(r5), Gap(r8).
  thompson-gap-witnesses-need-nonamenable-image: that proves the dimension-free gap 1/2 on the virtually solvable-image locus for the full family, using simplicity of V; its general form (A) applies to a single relator exactly when G0/<<r5>> has no nontrivial finite quotient, and this records the evidence for that hypothesis (no finite quotient of order below 443520 or acting on at most 16 points, no rank-2 image).
  thompson-v-not-lef: that is about exact local embeddings of V into finite groups; this is about exact homomorphisms of the larger one-relator groups G0/<<r5>>, G0/<<r8>> to finite and rank-2 linear groups.
  thompson-v-has-no-nontrivial-fd-unitary-representation: that excludes exact finite-dimensional unitary representations of V; this excludes exact rank-2 representations over every field, and small finite images, of the one-relator covers of V, where no simplicity is available.
artifacts:
  - experiments/thompson-v-relator-blind-2026-09-17/census.py
  - experiments/thompson-v-relator-blind-2026-09-17/validate_c.py
  - experiments/thompson-v-relator-blind-2026-09-17/log_m16.txt
  - experiments/thompson-v-relator-blind-2026-09-17/psl_search.py
  - experiments/thompson-v-relator-blind-2026-09-17/log_psl_V.txt
  - experiments/thompson-v-relator-blind-2026-09-17/pgl2c_exact.py
  - experiments/thompson-v-relator-blind-2026-09-17/log_pgl2c_V.txt
  - experiments/thompson-v-relator-blind-2026-09-17/log_pgl2c_CTRL2.txt
  - experiments/thompson-v-relator-blind-2026-09-17/pgl2_allchar.py
  - experiments/thompson-v-relator-blind-2026-09-17/log_pgl2_allchar.txt
  - experiments/thompson-v-relator-blind-2026-09-17/pgl2_char23.py
  - experiments/thompson-v-relator-blind-2026-09-17/log_pgl2_char23.txt
  - experiments/thompson-v-relator-blind-2026-09-17/simple_search.py
  - experiments/thompson-v-relator-blind-2026-09-17/log_simple_search.txt
  - experiments/thompson-v-relator-blind-2026-09-17/kb_r5.py
  - experiments/thompson-v-relator-blind-2026-09-17/log_kb_r5.txt
---

**ESTABLISHED** (exact computation plus a short written argument; unreviewed). All computations are exact
(integer, finite-field or algebraic-number arithmetic); nothing is numerical.

## Setting

`G0 = S4 *_<a> S3 = <a,b,c | a^2, b^3, (ab)^4, c^2, (ac)^3>` and `r5, r6, r7, r8` are the Bleak--Quick words of
`thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3`, read from `experiments/thompson-v-models/rel_V.txt`.
For a subset `S` of `{r5,...,r8}` put `Gamma_S = G0/<<S>>`, so `V = Gamma_{r5,r6,r7,r8}` and every `Gamma_S`
surjects onto `V`. Write `Gamma5 = Gamma_{r5}`, `Gamma8 = Gamma_{r8}`.

## Statement

1. **Parity.** `G0^ab = Z/2` (the sign `eta`: `a, c -> -1`, `b -> 1`). `eta(r5) = eta(r8) = -1` and
   `eta(r6) = eta(r7) = +1`. Hence `Gamma_S` is perfect whenever `S` contains `r5` or `r8`, and
   `Gamma_{r6,r7}` surjects onto `Z/2`.
2. **Rank 2, every field.** For every field `F`, every homomorphism `Gamma5 -> PGL(2,F)` and every
   homomorphism `Gamma8 -> PGL(2,F)` is trivial. Consequently every homomorphism to `GL(2,F)` is trivial, and
   no `PSL(2,q)` or `PGL(2,q)`, for any prime power `q`, is a quotient of `Gamma5` or `Gamma8`.
3. **Permutations.** No action of `G0` on a set of at most 16 points, other than the trivial one, satisfies
   `r5`; the same for `r8`. (Every action satisfying `r6`, `r7`, or both, on at most 16 points is trivial or
   factors through `eta`.)
4. **Small simple groups.** For `S` each of `U3(3)`, `L3(4)`, `U4(2)`, `U3(4)`, `U3(5)`, `J1`, `L3(5)`, every
   homomorphism `G0 -> S` with `r5 = 1`, or with `r8 = 1`, is trivial.
5. **Consequence.** Every nontrivial finite quotient of `Gamma5` or `Gamma8` has a nonabelian simple quotient
   of order at least `443520 = |M22|`, which is not of the form `PSL(2,q)` and has no faithful action on 16 or
   fewer points.

## Proofs

**(1)** In the abelianization (written additively) the relations read `2a = 0`, `3b = 0`, `4a + 4b = 0`,
`2c = 0`, `3a + 3c = 0`. The first three give `4b = 0` and `3b = 0`, so `b = 0`; the last two give `a = c`
(as `a = -a`, `c = -c`), leaving `Z/2` generated by `a = c`. The parities are the exponent sums of `a` and `c`
in the words, computed in `census.py` (the degree-2 action is `eta`, and the census reports that it satisfies
exactly `r6`, `r7`, `{r6,r7}`). A quotient of a perfect group is perfect.

**(2)** A field embeds in its algebraic closure, so take `F` algebraically closed. A homomorphism with `a -> 1`
forces `b^4 = b^3 = 1` and `c^3 = c^2 = 1`, so it is trivial. If `b -> 1` or `c -> a`, the image is a quotient
of `S3` or of `S4` and so acts faithfully on at most 4 points; item (3) excludes it. Otherwise:
- *Characteristic 0 or at least 5* (`pgl2c_exact.py`, `pgl2_allchar.py`). Normal form: `a = diag(1,-1)`,
  `c = c_t = [[t,t^2],[3,-t]]` with `t != 0`, and `b` one of `OCT+`, `OCT-` (faithful `S4`, over
  `Q(sqrt -2)`) or `S3` (`S4 -> S3`); the derivation of the normal form is in the docstring of
  `pgl2c_exact.py`. Each word gives three polynomials in `t` (the entries `M12`, `M21`, `M11 - M22`). Over
  `Q-bar` their gcd, after removing powers of `t`, is constant for `r5` and for `r8` in every class
  (`log_pgl2c_V.txt`). For `p >= 5` the norms to `Z[1/2][t]` have a common root mod `p` only if `p` divides
  the gcd of their pairwise resultants, a leading coefficient or a content. The only such primes `>= 5` are
  `5` (for `r8`, class `S3`), and there a direct gcd over `F_5` is constant (`log_pgl2_allchar.txt`). The
  same code finds the known solutions of `r6` (`t = 2 +- 2 sqrt 2 i` on `OCT+-`, `t = -2` on `S3`) and all four
  planted `PSL(2,17)` relators of the control file (`log_pgl2c_CTRL2.txt`).
- *Characteristic 3* (`pgl2_char23.py`). `ac` has order 3, so it is unipotent. This normalizes `c` to
  `[[1,1],[0,-1]]` with trivial residual torus. `b` is unipotent with `tr(ab)^2 in {0, 2 det(ab)}`, which gives
  four one-parameter families. In each family the gcd over `F_3[y]` for `r5` and for `r8` is constant.
- *Characteristic 2* (`pgl2_char23.py`). There are no elements of order 4 in `SL(2, F-bar_2)`, so `(ab)^2 = 1`.
  Normalizing `a = [[1,1],[0,1]]` and `c = [[0,1],[1,0]]` leaves `b = [[q, q^2+q+1],[1, 1+q]]`. The gcd over
  `F_2[q]` is constant for `r5` and for `r8`.
In every characteristic the controls `(bc)^5`, `(bc)^7` have solutions where they should. The exception is
family `N1` in characteristic 3, whose image is upper triangular, so `bc` is unipotent there. The `r6` solutions
appear in characteristics 2 and 3 as well.

A map to `GL(2,F)` with trivial projective image is scalar, so it factors through `eta` with scalar values
`+-1`. `r5` and `r8` have odd parity, so they map to `-1`, and the map is trivial.

**(3)** `census.py` enumerates every action of `G0` on `[m]`, `m <= 16`: an `S4`-set (a multiset of the 11
transitive `S4`-sets) together with every involution `c` with `(ac)^3 = 1`, enumerated through the `<a,c>`-orbit
types of sizes 1, 2, 3 and 6. `validate_c.py` checks the `c`-enumeration by brute force for `m <= 8`. At
`m = 16` alone, 9593374 actions are tested (`log_m16.txt`).

**(4)** `simple_search.py` builds each group as a projective matrix group by BFS from explicit generators:
- `SU(3,q)` from unitary transvections, over `F_{q^2}`;
- `Sp(4,3)` from symplectic transvections;
- `SL(3,q)` from elementary transvections;
- `J1` from Janko's two `7 x 7` matrices over `F_11`.
The group order is asserted: 6048, 20160, 25920, 62400, 126000, 175560, 372000. The search then fixes `a` at a
representative of each involution class and runs `b` over every element with `b^3 = 1`, `(ab)^4 = 1`, and `c`
over every involution with `(ac)^3 = 1`. Every homomorphism with `a != 1` is conjugate to exactly such a
triple. No triple satisfies `r5`, and none satisfies `r8` (`log_simple_search.txt`). As controls, the triples
satisfying `(bc)^k` are counted, and are zero exactly when the group has no element of that order along the
constrained pairs. For instance, `(bc)^5` gives 0 in `U3(3)`, whose order is prime to 5.

**(5)** A nontrivial finite quotient `Q` of the perfect group `Gamma5` has a maximal normal subgroup `M`, and
`Q/M` is simple and perfect, hence nonabelian simple. It is a quotient of `Gamma5`, and it contains an element
of order 3, since otherwise `b -> 1` and the image is a quotient of `S3`. The nonabelian simple groups of order
below 443520 are the following:
- `PSL(2,q)`, excluded by (2);
- `A5`, ..., `A9`, `L3(3)`, `M11`, `M12`, which act faithfully on at most 16 points and are excluded by (3);
- `Sz(8)`, whose order is prime to 3;
- `U3(3)`, `L3(4)`, `U4(2)`, `U3(4)`, `U3(5)`, `J1`, `L3(5)`, excluded by (4).
The list is the standard classification table of simple groups of order below one million. The next group
is `M22`. The same argument holds for `Gamma8`.

## What this changes

- **Class kill: relator-dropping gap proofs that avoid r5 and r8.** Take any argument for the defect gap of
  `thompson-v-mf-iff-opnorm-s4-s3-defect-gap-vanishes` that bounds only `max_{r in S} ||sigma(r) - 1||` for a
  subfamily `S` inside `{r6, r7}`.
  - *Invariant:* the parity `eta`.
  - *Step where it dies:* the exact one-dimensional representation `eta` is nontrivial and has
    `||eta(r6) - 1|| = ||eta(r7) - 1|| = 0`.

  So every proof of the gap must use `r5` or `r8`, in every dimension. In rank 2 and in every finite image of
  order below 443520, the joint relator `{r6, r7}` still has only the sign solution. Individually, `r6` and
  `r7` are satisfied far above the random-word rate:
  - in `U3(3)`, 129 and 225 triples against an expectation of about 0.7;
  - in `L3(4)`, 1217 and 449 against about 1.45;
  - in `U3(5)`, 2281 and 1561 against about 0.8.
- **One-relator strengthenings survive every exact test.**
  - `Gap(r5)` says that there is `epsilon > 0` with `||sigma(r5) - 1|| >= epsilon` for every nontrivial
    irreducible finite-dimensional unitary `sigma` of `G0`. `Gap(r8)` is the same for `r8`.
  - Each implies the gap for the full family, and hence that V is not MF.
  - `Gap(r5)` fails if `Gamma5` has any nontrivial finite quotient, or any nontrivial finite-dimensional
    unitary representation.
  - Items 2-5 show that no such failure exists among rank-2 representations over any field, or among
    finite quotients below order 443520.
  - If `Gamma5` has no nontrivial finite quotient, it has no nontrivial virtually solvable quotient. That is
    because it is perfect, and a virtually solvable group with no finite quotient is solvable. Then the
    general form (A) of `thompson-gap-witnesses-need-nonamenable-image`, applied with `R = {r5}`, already
    gives `||sigma(r5) - 1|| >= 1/2` on the whole virtually solvable-image locus, with one relator.
- **Calibration of the evidence (weak by design).**
  - `chi(G0) = 1/24 + 1/6 - 1/2 = -7/24`.
  - Near a generic point the representation variety of `G0` in `PGL(n)` has dimension about
    `7 n^2 / 24 + O(n)` modulo conjugation, while one relator imposes about `n^2 - 1` conditions. So a single
    long "random" relator is expected to have no nontrivial `n`-dimensional solutions for any `n >= 2`.
  - Over a finite simple group, the expected count is `|Hom_a(G0,S)| / |S|`, which is of order 1 (0.7 to
    1.45 above).
  - `r5` and `r8` behave exactly like random relators, and `r6`, `r7` do not. The zero counts are therefore
    consistent with `Gamma5` being far larger than `V`. They do not favour `Gamma5 = V` over a large
    one-relator group without small quotients.
- **Not established:** whether `r6, r7, r8` lie in `<<r5>>`, that is, whether `Gamma5 = V`.
  - A bounded shortlex Knuth--Bendix run (`kb_r5.py`, `log_kb_r5.txt`) did not reduce any of `r6`, `r7`, `r8`.
    It used rule length at most 22 and 36244 rules, and stopped after 775 s. The residues kept lengths 28, 26
    and 37 throughout. The system is not confluent, so this is inconclusive.
  - If `Gamma5 = V`, then V is a one-relator quotient of a virtually free amalgam of two finite groups, and
    `Gap(r5)` is equivalent to V not MF.
