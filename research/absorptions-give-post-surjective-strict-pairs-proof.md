---
rg: 2
id: absorptions-give-post-surjective-strict-pairs-proof
kind: route
title: Lift a finite change of the decoder output by keeping the absorbed coordinate fixed, and restrict or co-induce absorptions coset by coset
target: absorptions-give-post-surjective-strict-pairs
requires:
  - monomial-quantum-automata-are-topological-bernoulli-absorptions
  - capobianco-kari-taati-dual-surjunctivity-toolkit
---

Notation as in the target. The shift is `(g.u)_h = u_{g^-1 h}`. Configurations are asymptotic, `w ~ w'`, if they
differ on a finite set. For a subshift `Z` of `C^G` (`C` finite), a *sliding map* `F : Z -> D^G` is a continuous
equivariant map.

**Step 0 (finite memory).** Every sliding map `F : Z -> D^G` on a subshift `Z` has a finite memory set `M`:
`F(z)_g` depends only on `z` restricted to `gM`.
- `z -> F(z)_e` is continuous from the compact space `Z` to the finite set `D`, so it is locally constant.
  By compactness, finitely many cylinder sets cover `Z` on which it is constant. Let `M` be the union of
  their supports. Then `F(z)_e` depends only on `z|_M`.
- By equivariance, `F(z)_g = F(g^-1 z)_e`, which depends on `(g^-1 z)|_M`, that is on `z|_{gM}`.
- Consequence: if `z ~ z'` differ only on a finite `S`, then `F(z)` and `F(z')` differ only inside
  `{g : gM meets S} = S M^-1`, a finite set. So sliding maps send asymptotic pairs to asymptotic pairs.

This applies to `sigma = pr_1 Psi` on `A^G`, and to `Psi^-1` on the subshift `A^G x Y` of `(A x B)^G`.

**(i) Post-surjective.** Let `x in A^G` and `y' ~ sigma(x)`. Write `Psi(x) = (sigma(x), zeta)`, with
`zeta in Y`.
- `(y', zeta) in A^G x Y`, and `(y', zeta) ~ (sigma(x), zeta)`, since the two agree in the second coordinate.
- Put `x' = Psi^-1(y', zeta)`. By Step 0 applied to `Psi^-1`, `x' ~ Psi^-1(sigma(x), zeta) = x`.
- `sigma(x') = pr_1 Psi(x') = y'`.

So every configuration asymptotic to `sigma(x)` has a predecessor asymptotic to `x`. That is Definition 1 of
Capobianco-Kari-Taati.

**(i) Not injective.** Pick `y_1 != y_2` in `Y`, which exists because `|Y| >= 2`, and any `x`. Then
`Psi^-1(x, y_1) != Psi^-1(x, y_2)`, because `Psi^-1` is a bijection, and both have `sigma`-image `x`.

**(i) Not pre-injective.** By Capobianco-Kari-Taati Theorem 1, quoted verbatim in
`capobianco-kari-taati-dual-surjunctivity-toolkit`: "Every pre-injective, post-surjective cellular automaton on
a full shift is reversible." `sigma` is a cellular automaton on the full shift `A^G` (Step 0 and
Curtis-Hedlund-Lyndon), and it is post-surjective and not injective, hence not reversible. So it is not
pre-injective.

**(ii) Strict pair.** By (a) of `monomial-quantum-automata-are-topological-bernoulli-absorptions`, `Y` has a
shift-fixed point `y_0`, `tau(x) = Psi^-1(x, y_0)` is injective and not surjective, and `sigma o tau = id`. So
`(tau, sigma)` is a strict pair whose decoder is post-surjective by (i). By (i), `sigma` is post-surjective and
not pre-injective, which is exactly a failure of dual surjunctivity at alphabet `A`.

**(iii) Fixed-point rigidity.** Let `N` be normal in `G`.
- `u in A^G` is `N`-fixed iff `u` is constant on each coset `hN = Nh`. So `Fix_N(A^G)` is `A^{G/N}` with the
  `G/N`-shift. Likewise `Fix_N(Y)` is a closed subset of `B^{G/N}`. It is `G`-invariant, since
  `n g y = g (g^-1 n g) y = g y` for `y in Fix_N(Y)`. So it is a `G/N`-subshift, and it contains `y_0`.
- A pair in `A^G x Y` is `N`-fixed iff both coordinates are. By equivariance and injectivity, `Psi(u)` is
  `N`-fixed iff `u` is. So `Psi` restricts to a continuous bijection
  `A^{G/N} -> A^{G/N} x Fix_N(Y)`, which is `G/N`-equivariant and, by compactness, a homeomorphism.
- If `|Fix_N(Y)| >= 2`, this is an absorption over the group `G/N`. By (a) of the monomial theorem, applied to
  `G/N`, the group `G/N` is not surjunctive. Contrapositive: `G/N` surjunctive forces `Fix_N(Y) = {y_0}`.
- `N = G`: the trivial group is surjunctive, since an injective self-map of the finite set `A` is onto.
  So `Fix_G(Y) = {y_0}`.
- `G/N` sofic: by (ii), applied over `G/N`, an absorption over `G/N` would make `G/N` not dual surjunctive. That
  contradicts Capobianco-Kari-Taati Theorem 2 ("Let G be a sofic group. Every post-surjective cellular automaton
  on G is pre-injective"), quoted in `capobianco-kari-taati-dual-surjunctivity-toolkit`. So `Fix_N(Y) = {y_0}`.

**Notation for (iv).** For `H <= G`, `u in A^G` and `g in G`, write `u^g in A^H` for `(u^g)_h = u_{gh}`. Then
`u^{gh} = h^-1 . u^g` for `h in H`, and `(k . u)^g = u^{k^-1 g}`.

**(iv) Co-induction.** Let `Psi_H : A^H -> A^H x Y` be an absorption over `H`, with memory `M <= H` and local
rule `f`, and let `Psi_H^-1` have memory `M' <= H` and local rule `f'`, extended arbitrarily off the language.
- Define `Psi_G(u)_g = f((u_{gm})_{m in M}) = Psi_H(u^g)_e`. By `H`-equivariance of `Psi_H`,
  `Psi_G(u)_{gh} = Psi_H(h^-1 . u^g)_e = Psi_H(u^g)_h`. So `Psi_G(u)^g = Psi_H(u^g)` for every `g`.
- Let `Y_G = {b in B^G : b^g in Y for all g}`. It is closed, and it is shift-invariant because
  `(k . b)^g = b^{k^-1 g}`. `Psi_G` maps `A^G` into `A^G x Y_G`.
- Define `Phi(a, b)_g = f'(((a, b)_{g m'})_{m'}) = Psi_H^-1(a^g, b^g)_e`. As above,
  `Phi(a, b)^g = Psi_H^-1(a^g, b^g)`.
- Hence `(Phi o Psi_G)(u)^g = u^g` and `(Psi_G o Phi)(a, b)^g = (a^g, b^g)` for all `g`, so the two maps are
  inverse. Both are sliding block codes over `G`, so they are continuous and equivariant.
- `|Y_G| >= 2`: choose representatives `s_i` of the left cosets `s_i H`, and any `y_i in Y`. Put
  `b_{s_i h} = (y_i)_h`. Then `b^{s_i h} = h^-1 . y_i in Y`, so `b in Y_G`. Different families give different
  `b`, so `|Y_G| >= |Y| >= 2`.

**(iv) Restriction.** Let `Psi : A^G -> A^G x Y` be an absorption. By Step 0, `Psi` and `Psi^-1` have finite
memory sets `M` and `M'`. Let `H` be the subgroup they generate, and `Y_H = {y^e : y in Y}`, the restrictions of
`Y` to `H`. It is closed, as a continuous image of a compact set, and `H`-invariant.
- `Psi(u)_h` depends only on `u|_{hM}`, which lies in `H` for `h in H`. So `Psi_H(w) = Psi(u)^e`, for any `u`
  with `u^e = w`, is well defined. By equivariance `Psi(u)^g = Psi(g^-1 . u)^e = Psi_H(u^g)` for every `g`.
  `Psi_H` is continuous, `H`-equivariant, and maps `A^H` into `A^H x Y_H`.
- Likewise `Phi_H(a, b) = Psi^-1(a', b')^e`, for any `(a', b') in A^G x Y` with `a'^e = a` and `b'^e = b`, is
  well defined, because the memory `M'` lies in `H`.
- `Phi_H(Psi_H(w)) = Psi^-1(Psi(u))^e = w`, using the extension `(a', b') = Psi(u)`. Conversely,
  `Psi_H(Phi_H(a, b)) = Psi(Psi^-1(a', b'))^e = (a, b)`. So `Psi_H` is a homeomorphism
  `A^H -> A^H x Y_H`.
- `|Y_H| >= 2`: if `Y_H = {c}`, then every `y in Y` has `y^g = (g^-1 . y)^e = c` for every `g`. So `y` is
  determined by `c` on every left coset of `H`, and `Y` is a single point, a contradiction.

**(v) Multiples.** Let `C` be an alphabet with `|C| = m`. Then `Psi x id` is an equivariant homeomorphism
`(A x C)^G = A^G x C^G -> A^G x Y x C^G`, which is `(A x C)^G x Y` after reordering coordinates. `|A x C| = dm`.
