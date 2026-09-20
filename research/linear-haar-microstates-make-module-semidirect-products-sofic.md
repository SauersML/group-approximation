---
rg: 2
id: linear-haar-microstates-make-module-semidirect-products-sofic
kind: claim
title: Linear sofic codes (linear Haar microstates) of an F_p-module make its semidirect product sofic
distinct_from:
  dense-homoclinic-algebraic-actions-are-ce: that proves Connes embeddability of the Haar crossed product when the homoclinic group is dense; this proves group SOFICITY of the dual semidirect product under a strictly weaker linear-microstate hypothesis, which contains the dense-homoclinic case, the dense-periodic case and permutation modules over LERF actors.
  finite-field-point-models-give-the-rank-condition: that uses finite-field point models to verify a rank condition on skew group rings; this builds permutation sofic approximations of the group A semidirect Lambda itself from linear local codes.
  separating-sofic-quotient-sets-make-an-action-sofic: that is a criterion for soficity of set actions; this is a criterion for soficity of linear-module semidirect products, whose permutation-module case recovers the LERF mechanism.
  abelian-by-virtually-free-groups-are-sofic: that proves soficity for every module over a virtually free actor by amalgamation; this is a model-theoretic criterion valid over every sofic actor, including Kazhdan actors such as SL_3(Z).
  algebraic-compact-action-envelope-for-non-ce-relation: that is the open hole asking for a non-CE Haar algebraic crossed product; this is a fence on it, since every module with linear codes is excluded.
---

ESTABLISHED (unreviewed). DERIVATION [[linear-haar-microstates-module-semidirect-sofic-proof]].

## Statement

Let `Lambda` be a countable group, `p` a prime, and `A` an
`F_p[Lambda]`-module. Put `Gamma = A semidirect Lambda` with
`(a,lambda)(b,mu) = (a + lambda b, lambda mu)`.

**Definition (linear sofic code).** Let `Phi` be a finite subset of `A`,
`W` a finite subset of `Lambda` containing `e`, and `eps > 0`. A
`(Phi,W,eps)`-code consists of:

- a finite set `V` and a map `sigma : Lambda -> Sym(V)`;
- a finite-dimensional `F_p`-subspace `A_0` of `A` with
  `Phi union W Phi` contained in `A_0`;
- a finite-dimensional `F_p`-space `U` and linear maps `iota_v : A_0 -> U`
  for `v in V`;
- a set `G` of vertices with `|G| >= (1-eps)|V|` such that every `v in G`
  satisfies (C1)-(C3).

```text
(C1) sigma(lambda)sigma(mu)v = sigma(lambda mu)v  for lambda,mu in W;
     sigma(e)v = v;  sigma(lambda)v != v          for lambda in W\{e}.
(C2) iota_{sigma(lambda)^{-1} v}(a) = iota_v(lambda a)
                                                  for lambda in W, a in Phi.
(C3) iota_v(a) != 0                               for a in Phi\{0}.
```

`A` **has linear sofic codes** over `Lambda` if a `(Phi,W,eps)`-code exists
for every `(Phi,W,eps)`.

**Theorem (LSC).** If `A` has linear sofic codes, then `A semidirect Lambda`
is sofic, hence hyperlinear.

Given a code, the model is
`X = V x U` with `Pi(a,lambda)(v,u) = (sigma(lambda)v, u + iota_{sigma(lambda)v}(a))`.
It is a `(F, 3 eps)`-sofic approximation for
`F = {(a,lambda) : a in Phi, lambda in W}`.

## Dual form: linear Haar microstates

Codes are local, so `A` has codes iff every finitely generated submodule
does. Hence assume `A = F_p[Lambda]^m / R` and put `K = R^perp`, a closed shift-invariant
subgroup of `(F_p^m)^Lambda`. Pontryagin duality gives `hat K = A` and
`L^infinity(K, Haar) rtimes Lambda = L(A semidirect Lambda)`.

Here `Lambda` acts by `(lambda y)(mu) = y(lambda^{-1} mu)`, and the pairing
is `<c,y> = sum c_{mu,i} y(mu)_i`.

For `y in (F_p^m)^V`, a vertex `v` and a finite window `D` in `Lambda`,
define the local pattern

```text
y_v|_D in (F_p^m)^D,   y_v(mu) = y(sigma(mu)^{-1} v).
```

A **linear Haar microstate** for `(D, W, eps)` is a pair `(sigma, L)`:

- `sigma` satisfies (C1) on a `(1-eps)`-set `G` of vertices;
- `L` is an `F_p`-subspace of `(F_p^m)^V`;
- for every `v in G`, the local patterns are exactly the window projection of `K`:

```text
{ y_v|_D : y in L } = K|_D.                                  (LHM)
```

**Proposition (dual form).** `A` has linear sofic codes iff linear Haar
microstates exist for all `(D,W,eps)`. The code is

```text
U = L^*,   iota_v(c + R) = ( y -> sum c_{mu,i} y(sigma(mu)^{-1}v)_i ),
```

for `c` supported in a window. The inclusion `subseteq` in (LHM) makes
`iota_v` well defined, because `(K|_D)^perp = R intersect F_p[D]^m`. The
inclusion `supseteq` gives (C3).

Since each `v in G` has a surjective linear pattern map `L -> K|_D`, the
uniform measure on `L` has exactly Haar local statistics on `D` at every
vertex of `G`. These are therefore genuine linear Haar microstates of the
algebraic action in the sense of Hayes' local convergence.

## Classes with linear sofic codes

Each class below is proved in the route. `Lambda` is sofic in every case,
since (C1) forces it.

- **(E1) Free modules.** Take `L` to be all of `(F_p^m)^V`. This recovers
  soficity of `F_p^m wr Lambda`.
- **(E2) Submodules and directed unions.** Codes restrict to submodules, and
  they are local.
- **(E3) Amenable actors.** Take `V` a right-Folner set `F_n` and
  `L = K|_{F_n}`.
- **(E4) Dense periodic points** (`Lambda` residually finite). Suppose the
  union of `Fix_N(K)`, over normal finite-index `N`, is dense in `K`. Take `V = Lambda/N` and
  `L = Fix_N(K)`.
- **(E5) Dense homoclinic group** (`Lambda` sofic, `K_fin` dense). Take `L`
  to be the span of copies of finitely many finitely supported points of
  `K`, placed at every vertex of the sofic model. As a result, the conclusion
  of [[dense-homoclinic-algebraic-actions-are-ce]] upgrades for
  `F_p`-linear `K`: `hat K semidirect Lambda` is **sofic**, not just
  Connes-embeddable.
- **(E6) Permutation modules over LERF actors.** Let `Lambda` be LERF and
  `A = F_p[Lambda/Delta]` for any subgroup `Delta`. Use the truncated
  balanced product `U = F_p[(V x B)/~]` with `V = Lambda/H`. Here `B` is a
  large ball in `Lambda/Delta`, and the relation `~` is generated by
  `(sigma(lambda)^{-1}v, q) ~ (v, lambda q)`. (C3) reduces to separating a
  finitely generated subgroup `J` of `Lambda` (the image of the fundamental
  group of the finite Schreier ball) from finitely many elements outside it.
  In particular, for `Lambda` free and every normal `N`, the module
  `F_p[F/N]` has linear sofic codes, **whatever `F/N` is**. An "extraction
  lemma" (codes for `F_p[Q]` imply `Q` sofic) would therefore make every
  finitely generated group sofic. With `F/N` infinite simple, for example
  Thompson's `T`, (E6) lies outside (E4) and (E5).

## Use as a fence

For the hole [[algebraic-compact-action-envelope-for-non-ce-relation]], an
`F_p`-linear envelope `N -> L^infinity(K) rtimes Lambda` makes
`hat K semidirect Lambda` non-hyperlinear. Hence `hat K` must **fail** to
have linear sofic codes, i.e. fail (LHM) along every sofic model of
`Lambda`.

This strictly contains (DHA1). It also excludes, in one invariant:

- dense periodic points;
- every submodule or directed union of modules with codes;
- all permutation modules over LERF actors.

The converse (sofic `A semidirect Lambda` implies codes) is the separate
open hole
[[sofic-module-semidirect-products-have-linear-haar-microstates]].
