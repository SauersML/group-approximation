---
rg: 2
id: cornulier-tessera-host-self-similarity-proof
kind: route
title: Affine 3-adic states of Cornulier–Tessera's host stay integral and bounded, and translations are commutators
target: cornulier-tessera-host-is-rational-weakly-diagonal-self-similar
requires: []
artifacts:
  - research/artifacts/solve-bh-poly-dehn-2026-09-13.md
---

Notation as in the target: `A = 2I`, `B = [[2,1],[1,1]]`,
`Gamma_2 = Z[1/2]^2 x| <A,B>`, elements `(M,c)` with product
`(M,c)(M',c') = (MM', Mc' + c)`.

**1. Import.** Cornulier–Tessera arXiv:1003.0148, TeX l.135–136, verbatim:
"The group $\Gamma_n$ is finitely presented with quadratic Dehn function." At
TeX l.133: "it contains an obvious copy of $\BS(1,n)$, namely
$(\mathbf{Z}[1/n]\times\{0\})\rtimes(\mathbf{Z}\times\{0\})$". Take `n = 2`.

**2. The action is defined and preserves the tree.** Since `3` does not divide
`2`, `Z[1/2] ⊂ Z_3`. `det A = 4` and `det B = 1` are units in `Z_3`, so every
`M in <A,B>` lies in `GL_2(Z_3)`. An affine map `x -> Mx + c` with
`M in GL_2(Z_3)` and `c in Z_3^2` sends `x ≡ y mod 3^j` to
`Mx + c ≡ My + c mod 3^j`. So it acts on residues mod `3^j` compatibly in `j`,
that is, on the rooted tree with alphabet `X = {0,1,2}^2`.

**3. Faithful.** If `Mx + c = x` for all `x in Z_3^2`, then `x = 0` gives `c = 0`,
and then `M = I`.

**4. States.** Fix a first-level vertex `e in X` and write `x = e + 3x'`. Then
`(M,c)(e + 3x') = Me + c + 3Mx'`.
- Let `d in X` be the residue of `Me + c in Z[1/2]^2` mod 3. This is
  well-defined because `Z[1/2]/3Z[1/2] ≅ F_3`.
- Then `(M,c)(e + 3x') = d + 3(Mx' + u)` with `u = (Me + c - d)/3`.
- `u in Z[1/2]^2`: each entry of `Me + c - d` lies in `Z[1/2]` and has
  positive 3-adic valuation, hence lies in `3Z[1/2]`.

So the state of `(M,c)` at `e` is `(M,u)`, which lies in `Gamma_2`. The action
is self-similar, and states keep the linear part `M`.

**5. Rational.** By Zaremsky arXiv:2305.15176, TeX l.208, it suffices to check
the generators in `S`. Every generator `s = (M,c)` has `M in {A, B, I}` and
integral `c` with `|c|_∞ <= 1`.
- **States stay integral.** If `u in Z^2`, then `Me + u - d in Z^2` is
  divisible by 3 in `Z_3^2`. Since `Z^2 ∩ 3Z_3^2 = 3Z^2`, the next translation is
  integral again.
- **States stay bounded.** Write `‖M‖` for the maximal absolute row sum
  (2 for `A`, 3 for `B`, 1 for `I`), and `K = ‖M‖ + 1`. Entries of `e` and `d`
  lie in `{0,1,2}`, so `|Me + u - d|_∞ <= 2‖M‖ + |u|_∞ + 2`. If `|u|_∞ <= K`,
  the next translation has sup-norm at most `(3‖M‖ + 3)/3 = K`.
- Starting from `|c|_∞ <= 1 <= K`, induction on depth puts all states of `s`
  in the finite set `{(M,u) : u in Z^2, |u|_∞ <= K}`. So `s` is rational, and
  hence every element is.

**6. Weakly diagonal.** Zaremsky's definition (TeX l.229–230) asks that for
each `s in S` and each first-level state `s_e`, the element `s_e s^(-1)` has
finite order in `Gamma_2/[Gamma_2,Gamma_2]`.
- **States differ by translations.** With `s = (M,c)` and `s_e = (M,u)`:
  `s_e s^(-1) = (M,u)(M^(-1), -M^(-1)c) = (I, u - c)`.
- **Translations are commutators.** Put `a = (A,0)` and `τ_v = (I,v)` for
  `v in Z[1/2]^2`. Then `a τ_v a^(-1) = τ_(Av) = τ_(2v)`, so
  `[a, τ_v] = a τ_v a^(-1) τ_v^(-1) = τ_v`.
- So every translation is trivial in the abelianization, and in particular has
  finite order there.

**7. Finitely generated.** `a^(-k) τ_(e_i) a^k = τ_(2^(-k) e_i)`, and these
translations generate `Z[1/2]^2`. Together with `a` and `(B,0)`, which generate
the linear parts, `S` generates `Gamma_2`. This also follows from TeX l.133,
"Clearly, $\Gamma_n$ is finitely generated".

Steps 1–7 prove the three parts of the target.
