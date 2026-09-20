---
rg: 2
id: sp4-uq-free-subgroup-induced-quasireps-round
kind: claim
title: Quasi-representations of Sp4(Z) induced from free subgroups through finite actions round to homomorphisms on all of Sp4(Z), so the Burger-Ozawa-Thom mechanism cannot refute ultraproduct rounding
distinct_from:
  sp4-ultraproduct-quasireps-round-to-homs-at-one-scale: that is the open rounding statement (UQ) for every uniform quasi-representation into U(Q); this proves it only for the induced and block-monomial classes that a Burger-Ozawa-Thom counterexample would have to use, and decides nothing else.
  sp4-ssd-is-a-matrix-ultraproduct-winding-bound: that is the reduction and the rounding criterion; this checks item 2 of the failure modes of the open (UQ) node against it.
---

**ESTABLISHED** (route `sp4-uq-free-subgroup-induced-quasireps-round-proof`). Unreviewed.

Notation of `sp4-ultraproduct-quasireps-round-to-homs-at-one-scale`: `Gamma = Sp_4(Z)`, `Q = prod_n M_(n!)/c_omega`.
A finite-dimensional map `pi : Gamma -> U(d)` has defect `<= eps` on `W` if `||pi(g)pi(h) - pi(gh)|| <= eps` for
`g, h in W`. It is *block-monomial* over a finite set `X` if `C^d = sum_{x in X} V_x` and every `pi(g)` maps each
`V_x` onto some `V_{p_g(x)}`.

**Theorem.**
1. *(Honest permutation part.)* Fix a finite generating set `S` and a finite set of defining relators of length
   `<= R`. Let `pi` be unital and block-monomial, with defect `eps < sqrt 2` on a window `W` containing the word ball
   `B_R`. Then the maps `p_s` (`s in S`) define an honest action of `Gamma` on `X`, and `p_g` equals that action for
   every `g in B_R`.
2. *(Induction normal form.)* Let `pi` be unital, block-monomial over a transitive honest `Gamma`-set
   `X = Gamma/Lambda`, with defect `<= eps` on all of `Gamma`. Put `sigma(lambda) = pi(lambda)|_{V_{x_0}}`. Then
   `sigma` is a uniform `eps`-quasi-representation of `Lambda`, and there is a block-diagonal unitary `U` with
   `||U^* pi(g) U - Ind_Lambda^Gamma(sigma)(g)|| <= 2 eps` for every `g in Gamma`.
   - If `sigma` is `delta'`-close to a homomorphism of `Lambda` on the Schreier elements
     `t_{yx}^{-1} y t_x`, then `pi` is `(2 eps + delta')`-close on each `y` to an honest representation of `Gamma`.
3. *(Induction from free subgroups is roundable.)* Let `L` be a group such that every homomorphism from a
   finite-index subgroup of `Gamma` to `L` is trivial. This holds for every free group, by property (T), and for
   every torsion-free group with the Haagerup property. Let `X` be a finite `Gamma`-set, `c : Gamma x X -> L` an
   exact cocycle, and `sigma : L -> U(V)` any uniform `eps`-quasi-representation. Then the induced map
   `(pi(g) f)(x) = sigma(c(g, g^{-1} x)) f(g^{-1} x)` has defect `<= eps`, and it is within `eps` of an honest
   representation of `Gamma` on **all** of `Gamma`. The same holds for ultraproducts of such maps in `U(Q)`, with
   `M = Q`, `theta = id` and `delta = eps`.
4. *(Free patterns are trace-null.)* Let `X_n` be finite `Gamma`-sets, and `H <= Gamma` a subgroup of infinite
   index that is not contained in the centre `{+-1}`. Let `B_R` be the word ball. Then
   `lim_{R -> infinity} lim_omega |{x in X_n : Stab(x) cap B_R = H cap B_R}| / |X_n| = 0`.

**What this does to (UQ).** Item 2 of "How it can fail" in the (UQ) node asks whether a Burger–Ozawa–Thom (BOT)
construction, induced from a free subgroup `F <= Gamma`, can be realized in `U(Q)` at a fixed scale.
- *Literal realization.* Exact induction through finite `Gamma`-sets is realizable at every scale. By item 3 it rounds
  on all of `Gamma` with `delta = eps`. So it never refutes (UQ).
  - The named invariant is the class of the cocycle `c` in `H^1(Gamma on X; L)`, which equals
    `prod_{orbits} Hom(Lambda_j, L)/conj`.
  - It fails at the Shapiro step: `Lambda_j` has finite index, so it has (T), and every map to `L` is trivial.
  - The BOT cocycle lives on the infinite orbit `Gamma/F`, where the tautological class `id_F` is nonzero. Finite
    `Gamma`-sets cannot carry that orbit. By item 4, they cannot even imitate it on a set of positive trace.
- *General block-monomial models.* By item 2, a counterexample of this shape is an induced quasi-representation of a
  finite-index subgroup `Lambda`. That is a subgroup with the same stability problem as `Gamma`. The free subgroup
  drops out. Induction adds no new counterexamples: a block-monomial refutation of (UQ) with `M = Q` requires uniform
  quasi-representations of the `Lambda_n` that do not round on their Schreier elements.
- *Scalar blocks.* When `dim V = 1` the problem is the monomial parameter class. There the only obstruction left is a
  small real 2-cocycle with integral periods, whose bounded class is a multiple `t [b]` of the Kähler class
  (Burger–Monod). That is winding content, not the non-winding failure mode. This paragraph is a pointer and is not
  part of the theorem.

**What stays open.**
- Non-block-monomial maps into `U(Q)`.
- Block-monomial models whose defect is small only on the windows `W_n`. The ultraproduct allows these: items 2 and 3
  need defect `<= eps` on all of `Gamma`, or on a window containing the Schreier transversal. In the windowed case the
  model is an `eps`-almost-flat `U(V)`-local system on the finite cover of a presentation complex, and rounding means
  moving it to a flat one on the letter edges.
- Whether a BOT construction survives in a tracial ultraproduct at all. A trace on the C*-algebra of
  `Ind_F^Gamma sigma` gives a character of `Gamma` weakly contained in it. By Peterson's character rigidity, together
  with the isolation of finite-dimensional representations under (T), such a character must vanish off the centre.
  This paragraph is a heuristic, not proved here.
