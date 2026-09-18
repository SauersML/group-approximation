---
rg: 2
id: magnus-prepend-towers-are-amenable-quotients-of-the-group-proof
kind: route
title: The relative one-relator product is a pushout-functorial universal prepend step whose tower rebuilds the Magnus kernel, and a shift tower is the same thing as a homomorphism of G
target: magnus-prepend-towers-are-amenable-quotients-of-the-group
requires: []
---

Date: 2026-09-18. Written proof, not a Lean certificate. Notation as in the
claim; `a^s = s^(-1) a s`.

## 1. Functoriality

**Lemma 1.** Let `f : K -> L` be injective, `c' = f(c)`. Then
`P(L,c') = L *_K P(K,c)`, where `K -> P(K,c)` is the canonical map.

*Proof.* Both sides are presented by the generators of `L` and `X`, the
relations of `L`, and `W_0(X,c')`: the pushout of `L <- K -> P(K,c)` is
`(L * P(K,c)) / <<k = f(k)>>`, and `P(K,c)` is `K * <X>` modulo
`W_0(X,c)`. Identifying `K` with `f(K)` gives the presentation of
`P(L,c')`. ∎

**Corollary 1.** If `K -> P(K,c)` is injective, then `P(f) : P(K,c) -> P(L,c')`
is injective, and `L -> P(L,c')` is injective.

*Proof.* In an amalgamated free product `A *_C B` with `C` embedded in both
factors, both factors embed (normal form theorem). Here `C = K`, embedded in
`L` by `f` and in `P(K,c)` by hypothesis. ∎

`P` commutes with directed unions: if `K = U K_i` with `c` in `K_0`, then
`P(K,c) = colim P(K_i,c)` because presentations commute with directed
colimits, and the maps are injective by Corollary 1 when each
`K_i -> P(K_i,c)` is.

**Relative Freiheitssatz.** If `K` is locally indicable and `W_0(X,c)` is not
conjugate in `K * <X>` into `K` (true whenever `X` survives cyclic
reduction), then `K -> P(K,c)` is injective (Brodskii, *Sib. Math. J.* 1984;
Howie, *J. reine angew. Math.* 324, 1981).

**Failure over torsion coefficients at a singular extreme.** Take `n = 2`,
`W_0(a_0,a_1,a_2) = a_0 a_1 a_0^(-1) a_2` (exponent sum of `a_0` is zero),
`K = Z/6 = <g>`, `c_1 = g^3`, `c_2 = g^2`. In `P(K,c)`,
`X g^3 X^(-1) = g^(-2)`. Conjugating `(g^3)^2 = 1` gives `(g^(-2))^2 = 1`, i.e. `g^4 = 1`; with
`g^6 = 1` this gives `g^2 = 1`, hence `g^(-2) = 1` and then
`g^3 = X^(-1) g^(-2) X = 1`. So `g = g^3 g^(-2) = 1`: all of `K` dies. The
Freiheitssatz, and with it Corollary 1, fails over this amenable `K`. ∎

## 2. Circularity of the literal tower

Put `H_1 = B_0 = <a_0..a_n | W_0>` with chain `(a_0,...,a_n)`, and more
generally `H_k = <a_0,...,a_(n+k-1) | W_0,...,W_(k-1)>`, where
`W_j = W_0(a_j,...,a_(j+n))`, with chain `(a_0,...,a_(n+k-1))`.

**Lemma 2 (Magnus--Moldavanskii).** `H_(k+1) = H_k *_(F) B_k`, amalgamated
over `F = <a_k,...,a_(k+n-1)>`, which is free on these letters in both
factors (Freiheitssatz for `B_k` and, inductively, for `H_k`). In
particular `H_k -> H_(k+1)`, `a_j -> a_j`, and `H_k -> H_(k+1)`,
`a_j -> a_(j+1)`, are injective. (Standard: this is the structure of the
Magnus kernel; see Lyndon--Schupp IV.5.)

**The prepend identification.** `P(H_k, (a_0,...,a_(n-1)))` is
`<X, a_0, ..., a_(n+k-1) | W_0(X,a_0..a_(n-1)), W_0, ..., W_(k-1)>`.
Renaming `X -> a_0` and `a_j -> a_(j+1)` gives exactly `H_(k+1)`. Under this
renaming the complement inclusion `H_k -> P(H_k)` is the shift
`a_j -> a_(j+1)`, and `P(iota)` for the bottom-fixing inclusion
`iota : a_j -> a_j` is again bottom-fixing. Starting from
`H_0 = F(z_1..z_n)` with `z_i -> a_(i-1)`, which is injective because
`F_-` is free (Freiheitssatz), the prepend tower is `(H_k)`.

**Proposition 2.** The direct limit along the bottom-fixing inclusions is
`N_+ = <a_j (j >= 0) | W_j (j >= 0)>`, the shift `theta(a_j) = a_(j+1)` is
an injective endomorphism of `N_+`, and `N_+ *_theta = G`.

*Proof.* The limit statement is the union of the presentations; injectivity
of `theta` holds on each `H_k` by Lemma 2, hence on the union. The ascending
HNN extension is
`<a_j (j >= 0), tau | W_j (j >= 0), tau^(-1) a_j tau = a_(j+1)>`. By Tietze
moves, `a_j = tau^(-j) a_0 tau^j` eliminates all `a_j` with `j >= 1`, and
every `W_j` becomes a `tau^j`-conjugate of `W_0(a_0, a_0^tau, ...,
a_0^(tau^n))`. That leaves `<a_0, tau | W_0(a_0, a_0^tau, ..., a_0^(tau^n))>`,
which is the cyclic rewriting of `w`, i.e. `G` (with `a = a_0`,
`t = tau`). ∎

So the relative one-relator prepend, iterated from its free seed, rebuilds
`G`. Any other seed `K_0` gives `P`-towers whose limits map to
`N_+`-type groups receiving `G`, and the only information about `G` that
the construction can yield is the target group itself.

## 3. Universality: shift towers are homomorphisms of G

**Definition.** A *shift tower* is a triple `(H, theta, y)`: a group `H`, an
injective endomorphism `theta` of `H`, and `y in H` with
`W_0(y, theta(y), ..., theta^n(y)) = 1`. Its coordinate-0 window
representation is `rho : B_0 -> H`, `a_i -> theta^i(y)`.

**Every prepend-limit tower is a shift tower.** A prepend functor is any rule
`K -> Phi(K)` with a map `K -> Phi(K)` and a new letter `e` with
`W_0(e, c_1, ..., c_n) = 1`, where `c` is the bottom of the current chain.
By the universal property of `P`, each prepend step factors as
`K -> P(K,c) -> Phi(K)`, so `P` is the universal prepend functor. When the
limit `H_inf` satisfies `Phi(H_inf) = H_inf` (as in
[[bs12-amenable-square-chain-induced-tower-proof]] section 5, and in
Proposition 2 above), the complement inclusion is an injective endomorphism
`theta` with `theta(y_j) = y_(j+1)`, and `(H_inf, theta, y_0)` is a shift
tower whose window representation is the tower's coordinate-0 representation.

**Proposition 3.** (i) A shift tower `(H,theta,y)` gives a homomorphism
`pi : G -> A = H *_theta`, `a -> y`, `t -> tau`, with
`pi(a_i) = theta^i(y)` for `i >= 0`; `A` is amenable iff `H` is.
(ii) A homomorphism `pi : G -> Q` gives the shift tower
`(pi(N), theta, pi(a))` with `theta(h) = pi(t)^(-1) h pi(t)`, whose window
representation is `pi|_(B_0)` (through `a_i -> pi(a_i)`); `pi(N)` is
amenable if `Q` is.

*Proof.* (i) `tau^(-i) y tau^i = theta^i(y)` in `A`, so
`W_0(pi(a_0),...,pi(a_n)) = W_0(y, ..., theta^n(y)) = 1`, and `pi` is well
defined on `G = <a,t | W_0(a, a^t, ..., a^(t^n))>` (Proposition 2's Tietze
form). The kernel of `A -> Z` is the increasing union
`U_m tau^m H tau^(-m)` of copies of `H`, so `A` is amenable iff `H` is
(`H` embeds in `A`; amenability passes to directed unions and to extensions
by `Z`). (ii) `N` is normal, so `theta` is an automorphism of `pi(N)`, and
`theta^i(pi(a)) = pi(t^(-i) a t^i) = pi(a_i)`. Subgroups of amenable groups
are amenable. ∎

**Theorem (equivalence).** For finite sets `E_-, E_+, E_1` as in the claim,
the following are equivalent:
(a) some amenable shift tower has window representation `rho` with
`rho(E_-) cap rho(F_-) = rho(E_+) cap rho(F_+) = {}` and `1 not in rho(E_1)`;
(b) some homomorphism `pi : G -> Q`, `Q` amenable, has the same separation
on `B_0`.

*Proof.* (a) => (b): Proposition 3(i); the window representation of the
tower equals `pi|_(B_0)`. (b) => (a): Proposition 3(ii). ∎

So an amenable tower method witnesses (AA) for all finite sets iff (AA_G)
holds, and (AA_G) implies (AA) by restricting `pi` to `N`, whence `G` is sofic
by [[amenable-alphabet-magnus-shift-dictionary-sofic]].

## 4. Consequences for the relative one-relator step

* The proposed step asks for amenable quotients `Phi(K)` of `P(K,c)` with `K`
  embedded, functorial in `K`, and with the normal closure of `X` keeping
  `F_-` faithful. For `n >= 2`, `F_-` is free of rank `n >= 2`, so it cannot be
  **faithful** in an amenable group; only residual separation is possible,
  and that is exactly the finite-set form (a). By the theorem, (a) is a
  statement about amenable quotients of `G`; the tower adds a way of
  building them, not a weaker goal.
* Section 2 shows that the functorial, faithful choice `Phi = P` is
  available (Corollary 1 over locally indicable `K`) but returns `G`. Any
  amenable choice is a quotient of `P` that kills relations `G` does not
  have, and whether the separation survives is precisely (AA_G).
* Layers: by [[abelian-layer-alphabets-kill-magnus-pieces-of-rank-two]], the
  normal closure of `pi(a)` in `pi(<a_0..a_n>)` must have unbounded derived
  length or be non-solvable. By section 1, torsion (for instance locally
  finite) coefficient groups can break the Freiheitssatz at singular
  extremes, so the functoriality of Corollary 1 is not automatic for such
  layers.

## 5. Calibration

* `n = 1`, Baumslag--Gersten: (AA_G) holds by
  [[baumslag-gersten-elementary-amenable-quotient-keeps-a]] (`F_- = <a_0>`,
  and the quotient is faithful on `B_0 = BS(1,2)`). Proposition 3(i) is
  exactly how that result was obtained.
* Residually finite pieces: whenever `G` is residually finite, (AA_G)
  holds with finite `Q` if `F_-`, `F_+` are separable in `G`'s profinite
  topology; the theorem then says a tower exists, consistent with
  [[nonsingular-magnus-extremes-separable-piece-sofic]].
* The theorem proves no false statement: it asserts neither soficity nor
  residual amenability of any specific `G`.
