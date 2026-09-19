---
rg: 2
id: fpbs-mal-profinite-fold-density-is-finite-percolation-proof
kind: route
title: Derivations project along equivariant maps, bounded-depth closures are cylinder-approximable, and explicit seed intervals percolate cyclic and dihedral levels
target: fpbs-mal-profinite-fold-density-is-finite-percolation
requires: []
artifacts:
  - research/artifacts/fpbs-congruence-fold-census-2026-09-18.md
  - experiments/fpbs-congruence-fold-census-2026-09-17/dihedral_two_seeds.py
  - experiments/fpbs-congruence-fold-census-2026-09-17/dihedral_two_seeds_out.txt
---

The complete proofs are in §0 to §2 of
`research/artifacts/fpbs-congruence-fold-census-2026-09-18.md`. They import
only [[fpbs-mal-fold-closure-exactness]], which is ESTABLISHED, for the
inclusion `cl(A)` conull implies `E_K v b|_A = E_L`, and only in part (D).

1. **Lemma P0.** One closure step adds `y` iff, for one of the three triple
   positions `y` fills, the other two positions are in the set. This is a
   monotone formula in finitely many translates of `y`, and with multiplicities
   it is exactly the finite multiset rule. An equivariant `pi` commutes with it,
   so `cl_k(pi^{-1} S) = pi^{-1} cl_k(S)` for every `k`.
2. **(P).**
   - *Monotone and (<=).* These follow from P0.
   - *(>=).* Fix `k` with `mu(cl_k(A)) > 1 - eps`. Approximate `A` by a level-n
     cylinder to within `eps/|W_k|`, where `W_k` is the finite window of the
     `k`-step formula. The projected closure then covers `(1 - 2 eps)|Q_n|`,
     and the remaining points are added as seeds.
3. **(D).** `L_{j+1}` is the fold subgroup `<a, t_j a t_j^{-2}>` of the free
   basis `(a, t_j)` of `L_j`. Apply fold exactness to the free action
   `X∘phi^j`: `t_j|_A` promotes at cost `mu(A)`.
4. **(K1).** An interval of length at least `|alpha| + |beta|` gains the next
   residue, in the three cases `0 <= alpha < beta`, `alpha < 0 < beta` and
   `alpha = beta > 0`. The other cases follow by symmetry.
   `chi(t_{j+1}) = alpha - chi(t_j)`, so `chi∘phi^j` is never zero.
5. **(K2).** From `{(0,0), (0,1)}`, the triples of `(m, e)` and `(-m-1, e)`
   extend a full symmetric window `|k| <= m` to `|k| <= m + 1`. Moreover
   `t_j -> r^{-j} s`, and `s -> r^{-j} s`, `r -> r` is an automorphism.
   Exact enumeration agrees for `N = 2..15, 31, 64, 101`
   (`dihedral_two_seeds_out.txt`).
6. **Depth statement.** Pulled-back seed sets from a factor percolate by P0.
   So `sigma_b(X∘phi^j) <= r/|Q|` for every finite factor `Q` of `X∘phi^j`,
   and this is `O(1/N)` along K1 or K2 towers. Combine with (D).
