---
rg: 2
id: simple-group-width-over-congruence-targets-proof
kind: route
title: Cover the congruence kernel with two Singer tori by successive approximation, and match the big kernel block of near-scalar tuples with the nilpotent template
target: simple-group-width-over-congruence-targets
requires: [simple-group-psl-width-is-finite-field-linear-soficity, liebeck-shalev-normal-subset-covering, perfect-group-relator-width-over-nilpotent-groups, relator-width-over-nilpotent-by-locally-finite-groups, simple-group-relator-width-in-finite-simple-targets, relator-width-over-transitive-abelian-extensions]
artifacts: [research/artifacts/congruence-relator-width-part1-hensel-2026-09-13.md, research/artifacts/congruence-relator-width-part2-near-scalar-2026-09-13.md]
---

Full derivation in the two artifacts. Map of the argument:

## 1. The kernel (part 1, Sections 1 to 4)

- **Layers.** `K_j/K_(j+1) ≅ sl_n(F_q)`, and conjugation acts through the residue (Lemma 1.1).
- **Singer pair.** For `n >= 3`, or `n = 2` and `q >= 3`, there are `sigma_1, sigma_2 in SL_n(q)` of order prime
  to `p` with `C(sigma_1) ∩ C(sigma_2) = F_q · 1` (Lemma 2.1). Take a Singer element `sigma`, and conjugate
  it by a transvection, which normalizes no proper subfield of `F_(q^n)` when `n >= 3`. For `n = 2`, count
  the torus normalizer.
- **Layer surjectivity.** By the trace form, together with the order being prime to `p`,
  `(Ad_(sigma_1) - 1) sl_n + (Ad_(sigma_2) - 1) sl_n = sl_n` (Lemma 2.2).
- **Hensel lemma.** For lifts `g_i` of `sigma_i`, every `kappa in K_1` is `[g_1, b_1][g_2, b_2]` with
  `b_i in K_1`, by correcting one layer at a time (Lemma 3.1).
- **Covering.** If the residue class of `h` covers `PSL_n(q)` in `k_0` steps, then
  `SL_n(R) = Z_T Cons_(5 k_0)(h)` (Proposition 4.1).

## 2. The case split (part 1, Section 5; part 2)

With `P = max_x rho(abar_x)`, every template commutator `[u(a), v(a)]` lies in a bounded `Cons`:
- **`P = 0`.** The tuple lies in the nilpotent group `Z_T K_1`, so the nilpotent theorem applies.
- **`n < D`, `P >= 1`.**
  - For large `q`, Liebeck--Shalev in bounded rank plus Proposition 4.1.
  - For the finitely many small residue groups, `relator-width-over-nilpotent-by-locally-finite-groups`.
  - No soficity hypothesis. This is item 1 of the claim.
- **`n >= D`, `P >= n/(c_5 |X|)`.** The uniform collapse of (i) gives a relator far from the scalars.
  Then Liebeck--Shalev and Proposition 4.1.
- **`n >= D`, `1 <= P < n/(c_5 |X|)`.** Part 2:
  - the big block is an approximate homomorphism (Lemma 2.1);
  - it is matched by the nilpotent template with block-diagonal conjugators (Lemma 3.1);
  - the displacement seed is localized (Lemma 4.2);
  - a common free-summand localization (Lemma 4.3) puts everything in `SL_(d')(R)`, `d' = O(P)`, where
    Proposition 4.1 applies.

Every constant depends on `G` only (part 2, Section 6).

## 3. The equivalences

- **(i) => (ii).** Section 2. Tuples over `SL_n(R)/Z_0` lift to `SL_n(R)`.
- **(ii) => (i).** Take `R = F_q`. If `G` is linear sofic over finite fields, item (ii) of
  `simple-group-psl-width-is-finite-field-linear-soficity` fails.
- **(ii) => (iii).** Bounded width `K` gives `l(a_x) <= K max_r l(r(a))` for every bi-invariant length, as in
  part (C) of `simple-group-relator-width-in-finite-simple-targets`.
- **(iii) => (i).** If (i) fails, item (iii) of the PSL theorem fails, giving weak models into `PSL_n(q)`,
  which is `SL_n(F_q)/Z`.

## 4. Item 3: affine congruence groups

Let `Q = R^n x| SL_n(R)` with `A = R^n`, and write `N = <<R(a)>>`.
- **A relator with non-identity residue.** Let `h` be its linear part. Some `(h - 1) v` is unimodular,
  because `hbar - 1 != 0`. So `((h - 1) v, 1) = [r(a), (v, 1)] in Cons_2`.
  - `SL_n(R)` is transitive on unimodular vectors: a unimodular vector extends to a basis, and
    rescaling the last vector fixes the determinant.
  - Every vector is a sum of at most two unimodular vectors: if `w` is not unimodular, `w = e_1 + (w - e_1)`.
  - So `A <= Cons_4`. With the lifting of Section 2 of `relator-width-over-transitive-abelian-extensions-proof`,
    and item 2 over `SL_n(R)`, this gives `w_Q(a) <= K(G) + 4`.
- **Every relator value in `A x| K_1`.** That subgroup is the kernel of `Q -> SL_n(q)`, so it is normal.
  By (E1) every `a_x` lies in it, and it is a `p`-group. The nilpotent theorem gives `w_Q(a) <= max_x K(x)`.
