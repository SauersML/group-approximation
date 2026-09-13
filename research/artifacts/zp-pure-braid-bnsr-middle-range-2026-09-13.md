# BNSR invariants of pure braid groups: the middle range 2 <= m <= n-3 (2026-09-13)

Lane z1-09-pure-braid (Zaremsky Problem 1.9). Notation as in
`research/artifacts/zp-pure-braid-bnsr-top-range-2026-09-13.md` (Lemmas L, E, S and Theorem T there).
Status: Theorem P UNREVIEWED; Sections C–E are map and conjecture, not results.

## A. Theorem P (products of natural projections)

Let `A_1, ..., A_r <= [n]` be pairwise disjoint with `|A_i| >= 3`, and put `D = sum_i (|A_i| - 2)`. For each
`i` let `psi_i` be a character of `P_{A_i}` (`≅ P_{|A_i|}`) with `psi_i(Delta_{A_i}^2) = 0`, not all zero. Then

    chi = sum_i psi_i o phi_{A_i}   satisfies   [chi] notin Sigma^D(P_n).

In coordinates: `chi` is supported on pairs inside the blocks `A_i`, and on each block the coefficients sum
to zero. Examples: `r = 1`, `A = [m]` recovers the negative half of Zaremsky's Theorem 5.7 for every
zero-sum character of `P_m`, not only `chi_n^m`. Two disjoint triples in `P_6` with zero sums give
characters outside `Sigma^2(P_6)`. These lie in `Sigma^1(P_6)`, being on no KMM circle, so `D` is attained
there.

### A.1 Lemma LS (layered sections)

For `A <= [n]`, the homomorphism `(phi_A, phi_{A^c}): P_n -> P_A x P_{A^c}` is a split epimorphism.

*Proof.* Take `P_n = pi_1(Conf_n(C), p)`, `p = (1, ..., n)`. Let `p'` place the point with label `k` at `k + i`
for `k in A` and at `k - i` otherwise. The straight path from `p` to `p'` has no collisions and fixes
the identification `pi_1(Conf_n(C), p') = P_n`, compatibly with erasing strands. Put
`U_± = {±Im z > 0}`. The subspace `Conf_A(U_+) x Conf_{A^c}(U_-)` of `Conf_n(C)` contains `p'`: points in
disjoint open half-planes never collide. Its inclusion gives a homomorphism
`j: pi_1 Conf_A(U_+) x pi_1 Conf_{A^c}(U_-) -> P_n`. On this subspace, erasing the strands outside `A`
is the projection followed by `Conf_A(U_+) ⊆ Conf_A(C)`, which is a homotopy equivalence (`U_+` is an
open disc, and shrinking `C` into `U_+` deformation-retracts the configuration space). So
`(phi_A, phi_{A^c}) o j` is an isomorphism, and `j` composed with its inverse is a section. □

Iterating over `A_1`, then `A_2` inside `A_1^c`, and so on, and using `phi_{A_2} o phi_{A_1^c} = phi_{A_2}`,
gives a split epimorphism `P_n -> prod_i P_{A_i} x P_{rest}`. Projecting away `P_{rest}` shows that
`Phi = (phi_{A_1}, ..., phi_{A_r}): P_n -> prod_i P_{A_i}` is split.

### A.2 Proof of Theorem P

`P_{A_i} = H_{A_i} x Z` splits (Theorem T, proof), so `P_n -> Q := prod_i H_{A_i}` is split. `Q` has a finite
classifying space of dimension `D` (a product of the `(|A_i|-2)`-dimensional ones), and
`chi(Q) = prod_i (-1)^{|A_i|} (|A_i| - 2)! != 0` (Lemma L). The character `chi` factors as `psi o pi` with
`psi = sum_i psibar_i o pr_i != 0`. Lemma S gives `[chi] notin Sigma^D(P_n)`. □

Remark: Lemma S needs only a split quotient with a finite classifying space and nonzero Euler
characteristic, so the same works for any split quotient of `P_n` of that kind. Candidates beyond
products of natural projections: images of the above under outer automorphisms of `H_n` (the
`S_{n+1}`-symmetry of `M_{0,n+1}`; for `n = 4` it moves `P_3`-circles to the `P_4`-circle). The explicit
action on characters has not been written down and checked here.

## B. Characters known to lie in the middle invariants

1. Zaremsky, arXiv:1507.08597v1, Proposition 5.6: if `sum a_{ij} = 0`, exactly one `a_{ij}` is positive (or
   exactly one negative) and none is zero, then `[chi] in Sigma^{n-3}(P_n) \ Sigma^{n-2}(P_n)`.
2. Same paper, proof of Theorem 5.7 (via Lemma 1.4 and `ker phi_{[n-1]} = F_{n-1}`): a discrete character
   induced from `P_m` inherits the membership properties it has in `P_m`.
3. Kohno–Pajitnov, arXiv:1101.0437v2, Theorem 2.4: for an essential arrangement complement `M` in `C^l`
   and a positive `xi` (positive on every meridian), the Novikov homology vanishes in degrees `k != l`.
   Hence `±xi in Sigma^{l-1}(M, Z)` (Suciu arXiv:2010.07499v2, Section 13.4). For `M_{0,n+1}` in the chart
   `z_1 = 0, z_2 = 1` (hyperplanes `z_j = 0`, `z_j = 1`, `z_i = z_j`; `l = n - 2`), positivity means
   `a_{ij} > 0` for `(i,j) != (1,2)` and `a_{12} = -sum_{others}`. This is the homological version of item 1.
4. Center survives (Zaremsky, Corollary 3.8): `sum a_{ij} != 0` gives `Sigma^infinity`.

## C. Upper bound for the invariants (established by citation)

Suciu, arXiv:2010.07499v2, Section 13.1: arrangement complements are formal, so
`tau_1(V^q(M)) = R^q(M)`. Proposition 2.7 there: `tau_1^R(W) ⊆ Trop(W)`. Theorem 13.3(2): for
`1 <= q <= l - 1`, `Sigma^q(M, Z) ⊆ S(Trop(V^q(M)))^c`. Together,
`Sigma^q(P_n) ⊆ Sigma^q(P_n; Z) ⊆ S(R^q(P_n; R))^c` for `1 <= q <= n - 1`, where `R^q` is the degree-`q`
resonance variety of the Orlik–Solomon algebra of the braid arrangement. By propagation
(Denham–Suciu–Yuzvinsky, cited there), `R^1 ⊆ R^2 ⊆ ... ⊆ R^{n-1}`.

## D. Conjecture RS (resonance sharpness)

For all `n` and `m >= 1`: `Sigma^m(P_n) = S(P_n) \ S(R^{<=m}(P_n; R))`, where `R^{<=m}` is the union of
`R^i` for `i <= m`.

Evidence:
- `m = 1`: Koban–McCammond–Meier Theorem A plus Cohen–Suciu 1999 Proposition 6.9 (Suciu, Example 13.2).
- `m >= n - 2`: Theorem T. `R^{<=m}(P_n)` is the zero-sum hyperplane: `H^*(P_n) = H^*(H_n) ⊗ H^*(S^1)`; for
  zero-sum `a`, `H^{n-2}(H_n, a) != 0` because the Aomoto complex of `M_{0,n+1}` has nonzero Euler
  characteristic `(-1)^n (n-2)!`; for nonzero sum the complex is exact.
- Compatible with Theorem P: a character pulled back from a split quotient `Q` with nonzero Euler
  characteristic lies in `R^{<=D}(P_n)`. The split maps make the Aomoto complex of `(H^*(Q), psi)` a
  retract of that of `(H^*(P_n), chi)`, and the former has Euler characteristic `chi(Q) != 0`.

Caveat: Suciu Proposition 13.6 shows `Sigma^1 != S(R^1)^c` for the deleted `B_3` arrangement, where
translated tori occur. So RS is special to the braid arrangement. The safe form uses `Trop(V^{<=m})`,
and RS includes the claim that `V^m` of the braid arrangement has no translated components that
tropicalize outside `R^m`.

## E. Open computations and next steps

1. `R^{<=m}(P_n)` for `2 <= m <= n - 3`, explicitly. The first case is `n = 5`, `m = 2`: the Orlik–Solomon algebra of
   `A_4` has Betti numbers `1, 10, 35, 50, 24`. Predicted components are the five zero-sum 4-strand subspaces
   (Theorem P with `|A| = 4`) plus one more from the `S_6`-symmetry (characters with every row sum
   `sum_{j != k} a_{kj} = 0`), six 5-dimensional subspaces in all. Fibre-type tensor decomposition shows
   these are resonant in degree 2. The converse needs a nonresonance theorem (Yuzvinsky;
   Cohen–Dimca–Orlik) applied in every chart, plus a combinatorial lemma. Neither is verified here.
2. Membership: in the middle range, even `Sigma^2(P_5)` for characters with all "rows" nonzero is open.
   Tools: Novikov spectral sequence of `1 -> F_{n-1} -> H_n -> H_{n-1} -> 1` (for `chi` nonzero on the fibre
   `H_0` vanishes, so `H_{p+1}(H_n; Nov) = H_p(H_{n-1}; W)` with `W` a rank `n-2` Gauss–Manin-type module),
   Kohno–Pajitnov circle-valued Morse theory in other charts, and higher analogues of the KMM
   commuting-generator criterion.
