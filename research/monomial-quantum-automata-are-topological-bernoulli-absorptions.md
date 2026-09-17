---
rg: 2
id: monomial-quantum-automata-are-topological-bernoulli-absorptions
kind: claim
title: A group carries a strict diagonal-preserving monomial quantum automaton on M_d exactly when its full shift over Z/d is equivariantly homeomorphic to its product with a nontrivial subshift
distinct_from:
  stable-finiteness-failure-is-algebraic-bernoulli-absorption: that makes a one-sided inverse over F_p[G] into a continuous group isomorphism (F_p^n)^G -> (F_p^n)^G x X_P and proves the converse only among algebraic absorptions; this drops all algebra and shows that nonlinear topological absorptions A^G -> A^G x Y are the same thing as strict monomial quantum automata.
  strict-automata-yield-strict-quantum-endomorphisms: that asks whether any strict classical pair produces a strict quantum automaton and isolates the decoder conditions (D1) and (D2); this settles which decoders have a monomial extension, namely first coordinates of absorptions, and shows (D1) is then automatic.
  clifford-quantum-surjunctivity-iff-stable-finiteness: that classifies strict Clifford automata by one-sided inverses over F_p[G]; this classifies the larger monomial sector, with no linearity, prime dimension or group-ring input, and the Clifford examples diag(A, B^*) are its linear case.
  quantum-surjunctivity-conjecture: that asks about all quantum automata; this proves that on every surjunctive group every monomial diagonal-preserving automaton is onto, so a counterexample on a surjunctive group must be non-monomial.
  sofic-groups-are-qca-surjunctive: that proves QCA-surjunctivity for sofic groups by counting dimensions and records no implication between the quantum and classical conjectures; this supplies one implication, classical surjunctivity implies surjunctivity of the monomial sector, over every group.
---

**ESTABLISHED** by [[monomial-qca-topological-absorption-proof]].

**Setting.** `G` is a group, `d >= 2`, `A = Z/d`, and `zeta = e^{2 pi i/d}`. The algebra is `(x)_G M_d`, with Weyl
unitaries `X_g, Z_g`, where `X|j> = |j+1>`, `Z|j> = zeta^j |j>` and `ZX = zeta XZ`. The diagonal
`C(A^G) = C*(Z_g : g in G)` is identified with continuous functions of configurations `u in A^G`. A *quantum automaton*
is an equivariant, finite-propagation, unital *-endomorphism `Phi`. It is *strict* if it is not onto. It is
*monomial diagonal-preserving* if:

- `Phi(Z_e)` lies in `C(A^G)`, and
- `Phi(X_e)` normalizes the diagonal. Equivalently, `Phi(X_e)` is a diagonal unitary times a permutation unitary
  `U_pi|u> = |pi u>`, where `pi` permutes the patterns on a finite window.

A *topological Bernoulli absorption* over `(G, A)` is a subshift `Y` with `|Y| >= 2`, over any finite alphabet,
together with a shift-equivariant homeomorphism `Psi : A^G -> A^G x Y`.

**Theorem.** The following are equivalent.

1. `(x)_G M_d` carries a strict monomial diagonal-preserving quantum automaton.
2. There is a topological Bernoulli absorption `Psi : A^G -> A^G x Y`.
3. There is a cellular automaton `sigma : A^G -> A^G` that is not injective and has a *translation lift*: local
   bijections `T_e` of `A^G` with `T_e^d = id`, `T_e T_g = T_g T_e`, `lambda_g T_e lambda_g^-1 = T_g`, and
   `sigma o T_e = sigma + delta_e`.

The dictionary is explicit.

- (1) to (3): `Phi(Z_g) = zeta^{sigma(u)_g}`, and `T_g` is the permutation part of `Phi(X_g)`.
- (3) to (2): `Psi(u) = (sigma(u), T^{-sigma(u)} u)`, with `Y = sigma^-1(0)`. Here `T^x` is the continuous action of
  the compact group `(Z/d)^G` that the lift generates.
- (2) to (1): `Phi(X_e) = U_{T_e}` with `T_e(u) = Psi^-1(Psi(u) + (delta_e, 0))`, and
  `Phi(Z_e) = zeta^{(pr_1 Psi(u))_e}`.

Moreover, whenever the conditions hold:

- (a) **Strict pair.** `Y` has a shift-fixed point `y_0`. Then `tau(x) = Psi^-1(x, y_0)` is an injective, non-surjective
  cellular automaton on `A^G`, and `sigma = pr_1 Psi` satisfies `sigma o tau = id`. So `G` is not surjunctive.
- (b) **Decoder conditions.** `sigma_* mu = mu` for the uniform Bernoulli measure `mu`, and `Phi` restricts to
  `sigma^*` on the diagonal. So this decoder satisfies both (D1) and (D2) of
  `strict-automata-yield-strict-quantum-endomorphisms`.
- (c) **Strictness criterion.** A monomial diagonal-preserving automaton is onto if and only if its diagonal part
  `sigma` is injective.

**Consequences.**

- **Classical surjunctivity controls the monomial sector.** If `G` is surjunctive on `A^G`, then every monomial
  diagonal-preserving quantum automaton on `(x)_G M_d` is onto. Any counterexample to
  `quantum-surjunctivity-conjecture` on a surjunctive group must therefore be non-monomial.
- **Only the alphabet size matters.** Condition (2) depends only on `|A| = d`. The proof uses only the Weyl system of
  `A`, so `Z/d` may be replaced by any finite abelian group of order `d`, for example `F_p^n`.
- **Known strict automata are monomial.** The strict Clifford automata `diag(A, B^*)` of
  `clifford-quantum-surjunctivity-iff-stable-finiteness` are monomial and diagonal-preserving. So is the tree rule
  `X_v -> X_c X_c'`, `Z_v -> Z_c^h Z_c'^h` of `sofic-groups-are-qca-surjunctive`. The proof uses only a transitive
  symmetry of the site set, so it applies to both.
  - On the tree, the dictionary gives the absorption with `sigma(u)_v = h(u_c + u_c')`, where `T_v` adds `1` at both
    children.
  - In the Clifford case it recovers the algebraic absorption.
- **The chain of implications.** Write "absorbs" for "carries a topological Bernoulli absorption at some alphabet".
  1. `M_n(F_p[G])` not directly finite implies `G` absorbs at alphabet size `p^n`, by the algebraic absorption.
  2. `G` absorbs if and only if `G` carries a strict monomial automaton, by this theorem.
  3. Either of these implies `G` is not surjunctive, by (a).

**Open edges.**

- **Absorption question.** Does every non-surjunctive group absorb? Equivalently, does some strict pair have a decoder
  with a translation lift? A yes answer gives the full transfer of `strict-automata-yield-strict-quantum-endomorphisms`
  and makes Gottschalk equivalent, group by group, to surjunctivity of the monomial quantum sector.
- **Straightening.** Diagonal-preserving does not force monomial. On the tree, replacing `Phi(X_v)` by
  `Phi(X_v) W_v` gives a diagonal-preserving non-monomial extension of the same `sigma`. Here `W_v` is an order-`p`
  unitary in the relative commutant `C*(a, b) = M_p`, with `a = X_c X_c'^-1` and `b = Z_c^h Z_c'^-h`. Take
  `W_v = 1 + (zeta - 1) P`, where `P = p^-1 sum_k a^k`. It is swap-invariant, and each row has `p` nonzero entries.
  It is open whether every diagonal-preserving strict automaton can be straightened to a monomial one with the same
  diagonal part.
