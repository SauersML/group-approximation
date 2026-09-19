---
rg: 2
id: kazhdan-property-t-sigma1-proof
kind: route
title: Ozawa certificates upward, the Rabin amalgam and Serre's property FA downward
target: kazhdan-property-t-of-finite-presentations-is-sigma1-complete
requires: []
---

**Semidecidability.**  Let `P = <X | R>` be a finite (or finitely
generated recursive) presentation and `S = X u X^-1`.  By Ozawa's theorem
the group has (T) iff there are `lambda > 0`, finitely many
`xi_1, ..., xi_m in R[Gamma]` with `Delta^2 - lambda Delta = sum xi_i^*
xi_i`.  By the Netzer--Thom stability lemma (`c + 2^{2d-1} ||c||_1 Delta`
is a sum of squares for every hermitian `c` in the augmentation ideal
supported on words of length `<= 2^d`), if any real certificate exists
then a certificate with rational `lambda` and rational coefficients
exists.  A rational certificate is verified by expanding both sides as
formal sums over words and checking that the two sides agree as elements
of the group ring, i.e. by exhibiting finitely many derivations of word
equalities and a finite rational identity.  Enumerating all rational
certificates together with derivations halts iff the group has (T).

**Hardness.**  Fix a finitely presented `Gamma_0` with unsolvable word
problem and let `K(w)` be the Rabin group of
`Computability/RabinConstruction` (Lyndon--Schupp IV.4.1; Bajo §8).  If
`w = 1` then `K(w) = 1` (`rabin_trivial_of_word_eq_one`), which has (T).
If `w != 1`, `K(w) = G'' *_F G_2` with `F = <u, [w, s_0]> = <a, c>` free
of rank two and proper in both factors.  Suppose `K(w)` acted on the
Bass--Serre tree with a global fixed point: the point would be a vertex
(Bass--Serre actions have no inversions), whose stabilizer is a
conjugate of a factor, forcing `K(w)` to equal a proper subgroup.  So
`K(w)` fails property FA.  Watatani proved that (T) implies FA (an
action on a tree without fixed point gives an unbounded 1-cocycle in the
`l^2` space of edges, hence a representation with almost invariant but
no invariant vectors).  So `K(w)` fails (T).  Therefore
`w = 1 iff K(w) has (T)`, and `w |-> K(w)` is computable, giving
`Sigma^0_1`-hardness; complements give the `Pi^0_1` statement.
