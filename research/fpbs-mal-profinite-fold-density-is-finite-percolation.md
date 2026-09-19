---
rg: 2
id: fpbs-mal-profinite-fold-density-is-finite-percolation
kind: claim
title: The fold seed density of a profinite action of F(a,b) is the limit of the 2-of-3 percolation densities of its finite levels, and character or dihedral level towers force it to 0 at every depth
distinct_from:
  fpbs-weakly-bernoulli-fold-seeds-have-density-floor: that is a positive lower bound 1/80 on sigma_b for the Bernoulli weak class; this is an exact finite-level formula for sigma_b of profinite actions and an all-depth vanishing criterion, with no lower bound.
  fpbs-mal-fold-closure-exactness: that identifies generation with conull 2-of-3 closure for free actions; this computes the least closure density for profinite actions and uses exactness only for the depth bound Q_j <= sigma_b(X o phi^j).
  fpbs-mal-odometer-product-actions-have-cost-two: that uses the seed interval for chi(a) = 1 at depth 0; this extends the interval to every nonzero character, adds dihedral towers whose abelianization image is finite, and proves both stable under phi at every depth.
  fpbs-abert-nikolov-rank-gradient-equals-profinite-cost: that equates the full cost of a profinite action with a rank gradient; this is the analogous finite-level identity for the single-label fold density sigma_b, where finite levels compute the value exactly.
artifacts:
  - research/artifacts/fpbs-congruence-fold-census-2026-09-18.md
  - experiments/fpbs-congruence-fold-census-2026-09-17/dihedral_two_seeds.py
  - experiments/fpbs-congruence-fold-census-2026-09-17/dihedral_two_seeds_out.txt
  - experiments/fpbs-congruence-fold-census-2026-09-17/census_dih_out.txt
---

**ESTABLISHED** through `fpbs-mal-profinite-fold-density-is-finite-percolation-proof`.

**Setting.**
- Let `L = F(a, b)`, `phi(b) = b a b^{-2}`, `t_j = phi^j(b)`, `L_j = <a, t_j>`.
- For an L-set, the triples are `(y, a y, b y)`, counted with multiplicity.
  `cl` is the 2-of-3 closure.
- `sigma_b(X)` is the least measure of a set with conull closure.
- `r(Q)` is the least size of a percolating set of a finite L-set `Q`.
- `X∘phi^j` is `X` with `b` acting as `t_j`.
- `Q_j(X)` is the least cost of a graphing promoting `E_{X|L_{j+1}}` to
  `E_{X|L_j}`.

**Claim.**
1. **(P)** If `X = lim_n Q_n` is a profinite action along finite transitive
   L-sets `Q_n`, then
   `sigma_b(X) = lim_n r(Q_n)/|Q_n| = inf_n r(Q_n)/|Q_n|`.
2. **(D)** For every free action `X` and every `j >= 0`,
   `Q_j(X) <= sigma_b(X∘phi^j)`.
3. **(K1)** Let `chi : L -> Z` be nonzero with `chi(a) = alpha`,
   `chi(b) = beta`. Then `Z/N` with `a = +alpha`, `b = +beta` is percolated by
   `|alpha| + |beta|` consecutive residues, for every `N`.
4. **(K2)** The regular `D_N`-set with `a -> r`, `b -> s` is percolated by
   `{e, s}`, for every `N >= 2`.
5. **Depth statement.** Both K1 and K2 are stable under `phi`:
   - `chi∘phi^j` is never zero;
   - `D_N∘phi^j ≅ D_N`.

   So every free action with infinitely many such finite factors has
   `sigma_b(X∘phi^j) = 0` and `Q_j(X) = 0` for all `j`.

**Reading.**
- Along a profinite tower, the single-label part of the w10 hole W-prof is an
  explicit finite hypergraph invariant.
- Floor witnesses cannot have nonzero-character or dihedral level towers at
  any depth.
- The congruence census in the artifact (§3) gives certified upper bounds only.
  It shows the Sanov 3-, 5- and 7-adic towers plateau near 0.11, the same as
  random Schreier graphs, so congruence witnesses survive this test. That
  census is recorded as evidence and is not part of this claim.
