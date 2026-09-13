---
rg: 2
id: leavitt-commuting-units-are-algebraically-dependent
kind: claim
title: Any two commuting units of the binary Leavitt algebra over F_2 satisfy a nonzero polynomial relation
distinct_from:
  leavitt-unit-centralizers-have-finite-rank: that bounds the whole centralizer of each unit over its Laurent ring; this asks only that no second commuting unit be transcendental over it, which is weaker and still excludes H_3(Z).
  leavitt-units-of-infinite-order-have-linear-depth-growth: that is the metric premise about depth growth of single units; this is a commutative-algebra premise about pairs.
---

**OPEN.** Let `R = L_(F_2)(1,2)`. For all commuting `a, c` in `R^x` there is a nonzero Laurent polynomial
`P` in `F_2[x^(+-1), y^(+-1)]` with `P(a, c) = 0`. Equivalently, the group algebra `F_2[Z^2]` has no unital embedding into `R`.
A unital algebra map sends group elements to units, and it is injective exactly when the images of the two
generators satisfy no nonzero relation.

**Payoff.** By `leavitt-heisenberg-centers-have-infinite-centralizer-rank` (ii), `H_3(Z) <= R^x` would embed
`F_2[H_3(Z)]`, and with it its subalgebra `F_2[<a, c>] = F_2[Z^2]`, into `R`. So this claim excludes `H_3(Z)`
(`no-heisenberg-from-algebraic-dependence`), and through `kun-thom-wreath-nonembedding-from-no-heisenberg`
every Kun--Thom wreath over a Theorem E actor.

## Attempts

**From finite centralizer rank (route, not proved).** `leavitt-unit-centralizers-have-finite-rank` implies this
claim (`algebraic-dependence-from-finite-centralizer-rank`).

**Firewall: a proof decides an open question of Ara--Cortiñas over F_2.**
- `L_(F_2)(1,2)` is central simple, so `L ⊗ L` is simple, and every unital homomorphism `L ⊗ L -> L` is injective.
- Such a homomorphism would send `c ⊗ 1` and `1 ⊗ c`, for the north--south unit `c`, to commuting units. They are
  algebraically independent, because `F_2[c^(+-1)] ⊗ F_2[c^(+-1)]` is a Laurent ring in two variables and
  injects into `L ⊗ L`.
- So this claim implies `no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2`
  (`tensor-square-nonembedding-from-algebraic-dependence`). That is the case `k = F_2` of Ara--Cortiñas,
  arXiv:1108.0352v3, page 8, Question 5.7: "Is there a unital homomorphism φ: L_2 ⊗ L_2 → L_2?" This was checked
  against the PDF, and it is recorded as open on `leavitt-tensor-powers-are-left-coherent`.
- Conversely, a unital embedding `L ⊗ L -> L` over `F_2` would refute this claim and the finite-rank claim,
  without deciding `H_3(Z)`.

**Thompson and sampled units.**
- Commuting infinite-order Thompson elements with disjoint supports satisfy `(a-1)(c-1) = 0`.
- Units with centralizer `F_2[c^(+-1)]` plus torsion satisfy a relation with every commuting unit. This holds for
  the north--south unit, and exact computation suggests it for sampled linear units
  (`research/artifacts/leavitt-unit-centralizer-rank-2026-09-13.md`, Section 3).
- No general argument is known. For a linear unit with a large torsion-free centralizer, nothing forces a
  relation, and this is where the attempt stops.

**Linear north--south units (proved, lane `ex2-q34-commuting-units`).**
`leavitt-annulus-north-south-units-have-cyclic-centralizers` gives `C_R(u) = F_2[u^(+-1)]` for every unit with
clean prefix attraction and repulsion and a linear middle permuting clopen annuli. This includes non-Thompson
units such as `c(1 + n)` with `n` nilpotent in `s_10 R t_10`. So every commuting pair containing a conjugate of
such a unit is algebraically dependent.

**Persistent leading terms (task of this lane; not proved).** Let `u` have a persistent free-group leading term
`s_(νγ) 1_E t_ν` (`leavitt-free-group-leading-term-forces-linear-depth`).
- *What survives.* At a clean germ (`u s_ζ = s_(ζγ)`, `t_(ζγ) u = t_ζ`), the compression `t_ζ g s_ζ` of any
  `g ∈ C_R(u)` is a polynomial in `s_γ, t_γ`, and `g -> Σ ε_d t^d` is `F_2[u^(+-1)]`-linear into
  `F_2[t^(+-1)]`. See `research/artifacts/leavitt-annulus-north-south-centralizer-2026-09-13.md`, Section 6.
- *Where it dies.* A persistent leading term only gives an attracting ray for the leading part. Lower terms of
  `u` exit the ray and return to it, so no power of `u` has a clean germ. The compressions are not multiplicative,
  and elements with zero germ are not controlled. No substitute for the middle-region hypothesis is known.

**Relative commutants (a second route to Question 5.7).** `leavitt-endomorphism-relative-commutants-are-finite`
(open; proved for core and triangular units) decides Question 5.7 without passing through this claim.
