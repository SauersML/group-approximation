---
rg: 2
id: free-cover-left-right-action-over-sofic-group-is-sofic-proof
kind: route
title: A permutation frame on one coordinate and a sofic point on the other give commuting exact models with injective labels
target: free-cover-left-right-action-over-sofic-group-is-sofic
requires:
  - gkp-sofic-action-toolkit
---

GKP Definition 2.1(3), verbatim from arXiv:2401.04945v3 p. 3: `φ : G -> Sym(A)`
is an `(F,E,ε)`-orbit approximation of `α` if there are a finite set `B` and
`S <= A` with `|S| > (1-ε)|A|`, and for each `s in S` an injective
`π_s : E -> B` with `π_(φ(g)s)(x) = π_s(α(g^-1)x)` for all `s in S`, `g in F`,
`x in E`, whenever `φ(g)s in S` and `α(g^-1)x in E`. Definition 2.1(4): `Q` is
sofic if for all finite `F_Q <= Q` and `δ > 0` there are a finite set `A` and a
unital, `(F_Q,δ)`-multiplicative `σ : Q -> Sym(A)` with `d(1,σ(q)) > 1-δ` for
`q in F_Q \ {1}`.

Notation: `G = F x F'` acts on `Q` by `(u,v).x = φ_1(u) x φ_2(v)^-1`, so
`(u,v)^-1 . x = φ_1(u)^-1 x φ_2(v)`.

## Construction

Fix finite `F_G <= G`, `E <= Q` and `ε > 0`. Enlarge `F_G` so that it is a set
of pairs `(u,v)` of reduced words. Let `R` be the set of all prefixes of all
words `u`, `u^-1`, `v`, `v^-1` occurring in `F_G`, and let `F_Q <= Q` be the
finite set containing `E`, `E^-1 E`, the images of `R` under `φ_1` and `φ_2`,
and all products of at most four elements of these sets. Choose a sofic
`σ : Q -> Sym(A)` for `(F_Q, δ)`, with `δ` fixed below.

1. **Exact homomorphisms.** Define homomorphisms `λ : F -> Sym(A)` and
   `ρ : F' -> Sym(A)` on free generators by `λ(x) = σ(φ_1(x))` and
   `ρ(y) = σ(φ_2(y))`, extended freely.
2. **Frame space.** Let `Ω = Sym(A) x A` and

   ```text
   Φ(u,v)(s,p) = (λ(u) s, ρ(v) p).
   ```

   `Φ` is a homomorphism `G -> Sym(Ω)`. The two coordinates move different
   factors, so the images of `F x 1` and `1 x F'` commute exactly. In
   particular `Φ` is unital and `(F_G, ε)`-multiplicative.
3. **Labels.** Put `B = A` and, for `(s,p) in Ω` and `x in E`,

   ```text
   π_(s,p)(x) = s^-1( σ(x) p ).
   ```

## The good set

Let `A_good <= A` be the set of points `p` such that:

- (G1) for all `x != x'` in `E`, `σ(x) p != σ(x') p`;
- (G2) for all `(u,v) in F_G` and `x in E` with `y = φ_1(u)^-1 x φ_2(v) in E`,
  `λ(u)^-1 σ(x) ρ(v) p = σ(y) p`.

**Each condition fails on a fraction at most `Cδ` of `A`**, with `C`
depending only on `F_G` and `E`.

- (G1): `σ(x')^-1 σ(x)` agrees with `σ(x'^-1 x)` off a `2δ` fraction, by
  unitality and multiplicativity, as in GKP Lemma 2.13. `σ(x'^-1 x)` moves all
  but a `δ` fraction of points.
- (G2): write `u = x_1^(e_1) ... x_k^(e_k)` with `k` bounded by the word
  lengths in `F_G`. Then `λ(u)` is the product of the `σ(φ_1(x_i))^(e_i)`. By
  induction on `k`, using `(F_Q,δ)`-multiplicativity on prefixes and
  `d(σ(q)^-1, σ(q^-1)) < 2δ`, the permutations `λ(u)`, `λ(u)^-1`, `ρ(v)` agree
  with `σ(φ_1(u))`, `σ(φ_1(u)^-1)`, `σ(φ_2(v))` off a fraction `O(kδ)`. The
  same holds for their composites with `σ(x)`. Composing with bijections does
  not change these fractions. Then

  ```text
  σ(φ_1(u)^-1) σ(x) σ(φ_2(v)) p = σ(φ_1(u)^-1 x φ_2(v)) p
  ```

  off a further `O(δ)` fraction, since all factors lie in `F_Q`.

There are finitely many conditions, so `|A_good| > (1 - C'δ)|A|`. Choose `δ`
with `C'δ < ε`, and put `S = Sym(A) x A_good`, so `|S| > (1-ε)|Ω|`.

## Verification

- **Injective labels.** For `(s,p) in S`, `x -> s^-1(σ(x)p)` is injective on
  `E` by (G1), because `s^-1` is a bijection.
- **Equivariance.** Let `(s,p) in S`, `g = (u,v) in F_G` and `x in E`, with
  `g^-1 . x = y in E`. Then `Φ(g)(s,p) = (λ(u)s, ρ(v)p)` and

  ```text
  π_(Φ(g)(s,p))(x) = (λ(u)s)^-1( σ(x) ρ(v) p ) = s^-1( λ(u)^-1 σ(x) ρ(v) p )
                   = s^-1( σ(y) p )                          by (G2)
                   = π_(s,p)(g^-1 . x).
  ```

  This needs neither `Φ(g)(s,p) in S` nor any further hypothesis.

So `Φ` is a unital, `(F_G,ε)`-multiplicative, `(F_G,E,ε)`-orbit approximation.
The action is sofic. `∎`

## Goursat form

Let `L <= F x F'` with `p_1(L) = F` and `p_2(L) = F'`. Put
`N_1 x 1 = L ∩ (F x 1)`, `1 x N_2 = L ∩ (1 x F')` and
`θ : F/N_1 -> F'/N_2`, `θ(aN_1) = bN_2` for `(a,b) in L`. Take `Q = F/N_1`,
`φ_1` the quotient map, and `φ_2 = θ^-1 ∘ (F' -> F'/N_2)`. Then
`(a,b)L -> φ_1(a) φ_2(b)^-1` is a `G`-equivariant bijection
`(F x F')/L -> Q`. It is well defined because `(a,b) in L` iff
`φ_1(a) = φ_2(b)`, and surjective because `φ_1` is onto. Soficity of an action
is invariant under equivariant bijection (Proposition 2.9(2) of GKP, used
in [[gkp-sofic-action-toolkit]]).
