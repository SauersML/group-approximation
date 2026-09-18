---
rg: 2
id: thompson-f-every-twisted-binomial-is-ore-with-every-element
kind: claim
title: "In K[F], every twisted binomial 1 + lambda g with g ≠ 1 has a nonzero common right multiple with every nonzero element"
distinct_from:
  thompson-f-one-bump-binomials-have-common-multiples: that proves this for one-bump g; this asks it for every g ≠ 1, and the open cases have two or more bumps.
  thompson-f-amenable-iff-group-ring-is-ore: that is amenability of F as the Ore condition for all pairs; this is the Ore condition only for pairs with a binomial side, which amenability implies.
  thompson-f-binomial-multipliers-see-every-conjugate: that proves necessary conditions on multipliers and kills classes of methods; this is the full statement, still open.
---

**OPEN.** Let `K` be a field and `R = K[F]`. For every `g` in `F \ {1}`, every `lambda`
in `K^x` and every nonzero `b` in `R`, `(1 + lambda g) R ∩ b R ≠ 0`.

Equivalent forms:
- every binomial `alpha u + beta w` with `u ≠ w` and `alpha, beta ≠ 0` meets every
  principal right ideal, since `alpha u + beta w = alpha (1 + (beta/alpha) w u^-1) u`;
- the right `R`-module `R/(1 + lambda g) R`, induced from the character `g -> -1/lambda`
  of `<g>`, is a torsion module.

**Why it matters.**
- If `F` is amenable, this holds (`thompson-f-amenable-iff-group-ring-is-ore`).
- A counterexample is a non-Ore pair, so it would prove `thompson-f-is-not-amenable`.
- A proof excludes every non-Ore witness with a binomial side. A proof of non-amenability
  through the Ore condition would then need both sides with at least three terms, such as
  `Q_4` with two full trinomials over a field other than `F_2`, or generic `P_(2,2)`
  (`research/artifacts/thompson-f-certificate-shapes-2026-09-12.md` §4).

**Reductions.**
- *Families of conjugates.* For fixed `g` and `lambda`, the statement for every `b` holds
  iff every finite family of conjugates has `∩_t (1 + lambda t^-1 g t) R ≠ 0`. "If": for
  `v` in the intersection over `t` in `supp b`, `b v` lies in `(1 + lambda g) R`, because
  `t (1 + lambda t^-1 g t) = (1 + lambda g) t`. "Only if": apply the statement to each
  conjugate against the running multiple.
- *Counting.* It suffices that for every finite `B ⊆ F` some finite `S ⊆ F` meets fewer
  than `|S|` right cosets `<g> t s` with `t` in `B` and `s` in `S` (certificate-shapes
  artifact §4 item 2).

**Established cases.**
- one bump, against every `b` (`thompson-f-one-bump-binomials-have-common-multiples`);
- several bumps, against `b` in `K[H_i × Z_i]`
  (`thompson-f-multibump-binomials-meet-stabilizer-ideals`);
- several bumps with dyadic endpoints, against `b` in the group ring of the pointwise
  stabilizer of the bump endpoints
  (`thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals`, unreviewed);
- `lambda = -1` against binomials `b` (`thompson-f-binomial-pairs-have-common-multiples`,
  item 3).

## Attempts

- **Local-to-global nesting through stabilizers (dead).** For one bump, the families of
  conjugates are handled by sorting along a common right endpoint and applying local
  property O inside nested bump groups
  (`thompson-f-rescaled-x0-binomials-have-common-multiples-proof`, Item 1). For two bumps,
  conjugates have different interior endpoints. Dies: if `c` moves `z`, then
  `(1 + lambda c) R ∩ K[Stab_F(z)] s = 0` for every `s`, because each right coset `<c> f`
  meets `Stab_F(z) s` in at most one element (Remark in
  `thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals-proof`). So a running multiple
  for earlier conjugates never lies in the local group ring of a later conjugate with a
  different endpoint, and any proof must use multipliers that move endpoints.
- **Separating the bumps (dead).** In `K[<g_1, g_2>] = K[x^{+-1}, y^{+-1}]` the element
  `1 + lambda x y` is irreducible, so it divides no product `p(x) q(y)` of nonzero Laurent
  polynomials. Every module obtained from modules `K[x^{+-1}, y^{+-1}]/(p(x))` and
  `K[x^{+-1}, y^{+-1}]/(q(y))` by submodules, quotients and extensions has an annihilator
  containing such a product. So `K[<g_1, g_2>]/(1 + lambda g_1 g_2)` is not built from
  one-bump modules, and induction from `<g_1, g_2>` cannot reduce the problem to one bump.
- **Other bumps as coefficients (dead as stated).** With `g_2` central in
  `F_[0,m] × <g_2>`, the field `K(z)` trick settles `b` in that subgroup ring
  (`thompson-f-multibump-binomials-meet-stabilizer-ideals`). For general `b` the second bump
  is not central, and using `K[F_[0,m]]` as a coefficient ring would need dimension counts
  over `K[F_[0,m]]`, which is the Ore condition for a copy of `F`.
- **Shifting with the centralizer (dead).** Only leftmost powers of `g` give scalar
  congruences modulo `(1 + lambda g) R`. As a right module `R/(1 + lambda g) R` has basis
  the cosets `<g> w`, and for `z` in `C_F(g)` outside `<g>` left multiplication sends the
  coset `<g> w` to the different coset `<g> z w`. So a count cannot strip commuting elements
  such as `g_1 g_2^-1`, even though conjugation by them pushes both sides of a shared
  endpoint toward it.
- **Opposite orientations (partial reduction, open).** Let `g = g_1 g_2` with bumps
  `(p, m)` and `(m, q)` sharing a dyadic endpoint `m`.
  - *Same orientation* (both below or both above the diagonal): conjugation by `g` and by
    `g^-1` each contracts one side of `m` and expands the other, so a monomial moving `m`
    is never pushed into a small region.
  - *Opposite orientations*: `g^-1` moves the points of both bumps toward `m`. Factor out
    powers of `g_1` and `g_2` to kill the germs at `p` and `q` (index trick at both outer
    endpoints), then conjugate by `g^-K`. Every monomial of `b`, including those moving `m`,
    lands in `F_[m-delta, m+delta]`, where `h -> g^-1 h g` is conjugation by the two-sided
    affine expansion of `g` at `m`, the analogue of Step 4 of Proposition 1.
  - Missing: a submonoid `P` of `F_[m-delta,m+delta]` such that every finite subset has a
    right translate inside `P`, `P` is invariant under that two-sided zoom, and `P` has
    unique normal forms whose letter depths satisfy the insertion bound of the one-bump
    count. With such `P`, steps 5c–5g of
    `thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals-proof` would run with
    crossing letters of every depth inside the window. The one-sided monoid `M` does not
    work: its nontrivial elements all move points near the right endpoint.
- **Global count with an endpoint-moving shift (open).** The one-bump count factors out
  powers of `g`, pushes the rest into the affine end of the bump, and counts positive normal
  forms in a letter window shifted by conjugation. The product count of
  `thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals-proof` does this in every bump
  at once, but only for monomials that fix the endpoints. An element moving an interior
  endpoint `z` is not pushed into any bump: conjugation by powers of `g` moves `f(z)` toward
  an endpoint while `z` stays fixed. What is missing is a normalization of `g` and a
  submonoid `P` with `F = P P^-1`, closed under conjugation by `g`, whose letter windows
  still grow polynomially under that conjugation. No such `P` is known.
- **Mackey support obstruction (2026-09-17, obstruction; proves no case).** Split
  `R/(1 + lambda g) R` over the double cosets `<g> w V`. On a free double coset
  (`V ∩ w^-1 <g> w = 1`) the coset test turns `b v` into `beta v` for a nonzero `beta` in
  `K[V]`. Proved in `thompson-f-binomial-multipliers-see-every-conjugate`:
  - (1) any multiplier `v` with `b v` a nonzero element of `J` generates, through
    `V_v = <x y^-1 : x, y in supp v>`, a group containing a nontrivial power of `t^-1 g t`
    for every `t` in `supp b°`, so `Fix(V_v) ⊆ ∩_t Fix(t^-1 g t)`;
  - (2) transverse factors (`K[A]` with `A` meeting no conjugate of `<g>`, for instance
    one-bump twisted binomials when `g` has `>= 2` bumps) can be divided out of `y a` in `J`;
  - (3) for `V` normalized by `g` with `V ∩ <g> = 1` and `b` in `K[V]`, multipliers in
    `K[<g> V]` exist iff the shifts `phi^a(b)` are right linearly dependent over `K[V]`.

  Classes killed:
  - nesting in any subgroup that lacks powers of all the conjugates, which contains the dead
    stabilizer nesting;
  - every Guba-type shift count whose coefficients `r_a` fix a fixed point `z` of `g` (or
    `u(z)` after a left prefactor `u`), against any `b` with a monomial sending `z` into
    `supp g`. This covers steps 5c–5g with `M` or `M × M`;
  - reduction to the one-bump product class for multi-bump `g`.

  Where it survives: the opposite-orientations case is exactly zoom-orbit dependence of
  `g^-a b g^a` over `K[<g_1> F_c(p,q)]`, with coefficients whose support groups move `m`.
  The missing monoid `P` must contain crossing letters.
