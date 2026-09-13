# Low-dimensional linear representations of the (A_7, A_7, A_8) triangle candidates

Lane `ex-hyperbolic-triangle-search`, 2026-09-13. Computed on MSI with Sage 10.7 (libgap, and
Singular for Gröbner bases). The code is `experiments/hyperbolic-triangle-search/lin4.py`; the
outputs are `lin4_cal.out` and `lin4_cands.out`. The groups `G_1..G_4` are those of
`hyperbolic-triangle-quotient-search-2026-09-13.md` §1.

## 1. Why linear representations

- A nontrivial finite quotient of `G` gives a nontrivial homomorphism `G -> GL_d(K)`, from a
  faithful representation of the quotient.
- Conversely, a nontrivial homomorphism `G -> GL_d(K)` has a finitely generated linear image.
  By Mal'cev's theorem that image is residually finite, so `G` has a nontrivial finite quotient.
- A representation over any field extends to its algebraic closure. So deciding
  `Hom(G, GL_d(K̄))` for `K̄` algebraically closed covers every field of that characteristic.

Low dimension is where rigid representations live. This is how Caprace–Conder–Kaluba–Witzel
found `PSp_6(p)` quotients that small-quotient searches missed (their Remark 5.16).

## 2. Dimension 4, characteristic 2: the reduction

Let `K = F̄_2` and suppose `φ: G -> GL_4(K)` is nontrivial.
- **(a) Modules.** `φ` is injective on `A`, `B`, `C`. The 2-modular irreducibles of `A_7` and `A_8`
  of dimension at most 4 are `1, 4, 4*` (ATLAS of Brauer characters, recalled rather than
  re-derived). A faithful 4-dim module therefore has a composition factor `4` or `4*`, so it is
  that irreducible. Both are defined over `F_2`: `A_8 ≅ L_4(2)` via GAP
  `IsomorphismGroups(AlternatingGroup(8), SL(4,2))`, and `A_7` is the stabiliser of the point 8.
  Up to conjugacy there are `2^3` type triples `(ε_A, ε_B, ε_C)`.
- **(b) Eigenvalues.** An element of order 7 acts on `4` with eigenvalues `{1, ω^a, ω^{2a}, ω^{4a}}`, where
  `ω ∈ F_8` is a primitive 7th root of 1. The edge generators must have equal characteristic
  polynomials from both sides: `φ(q)^{e1}` from `A` and from `B`, and likewise for `r^{e2}` and `p^{e3}`.
- **(c) Torus parametrisation.** Fix `α = φ|_A = ρ_{ε_A}` and `t = α(y_A)^{e1}`, which has 4 distinct eigenvalues.
  - Every `β` of type `ε_B` with `β(x_B) = t` is `g β_0 g^{-1}` with `g = S H S'^{-1}`, where `S`, `S'` are
    eigenbases of `t` and `β_0(x_B)` with the same eigenvalue order. Here
    `H = diag(h_1, h_2, h_3, 1)`, since scalars act trivially.
  - In the `t`-eigenbasis, `u = φ(r)^{e2} = H M H^{-1}` with `M = S'^{-1} β_0(y_B)^{e2} S'`, and
    `v = φ(p)^{e3} = N = S^{-1} α(x_A)^{e3} S`.
- **(d) Necessary trace equations.** `(u, v) = (γ(x_C), γ(y_C))` for some `γ ≅ ρ_{ε_C}`, so for
  every word `w` we need `tr w(u, v) = tr w(ρ_{ε_C}(x_C), ρ_{ε_C}(y_C))`. Used: `tr(u^i v^j)` for `1 <= i, j <= 6`
  and `tr(u^i v^j u^k v^l)` for `1 <= i, j, k, l <= 3`. That is 117 equations in `h_1, h_2, h_3, g_1, g_2, g_3`
  over `F_8`, together with `h_i g_i = 1`.
- **(e) Decision.** If the Gröbner basis of this ideal is `[1]`, no `φ` of this type exists. Otherwise the
  points of a 0-dimensional ideal are computed and checked against all relators of `C`.

## 3. The eigenvalue sign obstruction

Let `χ` be the Legendre symbol mod 7. For `g` of order 7 in `A_7` or `A_8` acting on `4`, set
`τ(g) = χ(a)` in the notation of (b). This is well defined because `{1,2,4}` are the squares mod 7.
- On `4*`, `τ` changes sign.
- `τ(g^e) = χ(e) τ(g)`.

Matching eigenvalues on the three edges gives
- `ε_A τ(y_A) χ(e1) = ε_B τ(x_B)`;
- `ε_B τ(y_B) χ(e2) = ε_C τ(x_C)`;
- `ε_A τ(x_A) χ(e3) = ε_C τ(y_C)`.

Multiplying them,

`σ(G) := τ(x_A) τ(y_A) τ(x_B) τ(y_B) τ(x_C) τ(y_C) χ(e1 e2 e3) = +1`.

**Lemma.** If `σ(G) = -1`, then `G` has no nontrivial 4-dimensional representation in
characteristic 2. If `σ(G) = +1`, exactly two type triples pass (b): `ε_A` is free and fixes the other two.

The obstruction depends only on classes and exponents, not on the positions of the edge
groups. So a random choice of twists kills such a triangle in this whole family of targets with
probability `1/2`. Permutation searches cannot see it, because 7-cycles are rational
(all their powers are conjugate).

## 4. Results (`lin4_cands.out`)

`ε = 0` is the module `4` given by the GAP isomorphism, and `ε = 1` is its dual.

| candidate | `σ` | type triples passing (b) | trace ideal | `Hom(G_i, GL_4(K))`, `char K = 2` |
|---|---|---|---|---|
| `G_1` | `+1` | `(0,0,1)`, `(1,1,0)` | `(1)`, `(1)` | trivial |
| `G_2` | `-1` | none | — | trivial |
| `G_3` | `+1` | `(0,0,0)`, `(1,1,1)` | `(1)`, `(1)` | trivial |
| `G_4` | `-1` | none | — | trivial |

**Calibration** (`lin4_cal.out`, 3.1 s):
- **Literal `(A_8, A_8, A_8)` triple** `(1,5,2,4,7,6,8), (1,6,4,7,2,5,3), (1,5,4,8,2,3,7)` (seed 20260913), `e = (1,1,1)`.
  Two type triples pass. Each trace ideal is 0-dimensional with 1 point over `F_8`, and that point
  satisfies all relators of `C`.
- **Literal `(A_7, A_7, A_7)` triple** of `tri_cal2.g` with twisted pairs `(p,q), (q^3,r), (r^5,p^2)`,
  `e = (3,5,2)`. Two type triples pass, each with 2 points, all verified.

**Conclusion.** For every field `K` of characteristic 2 and each `i`, every homomorphism
`G_i -> GL_4(K)` is trivial. So no `G_i` has a nontrivial finite quotient with a faithful
4-dimensional representation in characteristic 2. This excludes every subgroup of
`GL_4(2^m)` generated by copies of `A_7` and `A_8`, for all `m`. The proof is computer-assisted
and unreviewed.

**Scale.** Dimension 4 in characteristic 2 is the smallest dimension of a faithful
representation of `A_8` over any field. In characteristic 0 or odd characteristic the minimum is 7
(recalled from the character tables). The heuristic expected dimension of the representation variety
modulo conjugation is `3·15 − 3·12 − 15 = −6`.

## 5. Next

- **`d = 6`, characteristic 2.** `A_7` and `A_8` act on the 6-dimensional heart of `F_2^8`; only
  irreducible restrictions are covered.
- **`d = 7`, characteristic 0 and `p ≡ 1 mod 7`.** `A_7` acts on `F^7 = 6 + 1` and `A_8` on the 7-dimensional heart.
  These are the only faithful 7-dimensional modules in characteristic 0, so this case gives all of
  `Hom(G_i, GL_7(C))`.

The code is `linD.py`.
