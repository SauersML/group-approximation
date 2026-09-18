---
rg: 2
id: thompson-f-exact-shift-covariant-models-force-amenability
kind: claim
title: Shift-covariant unitary models of Thompson's F reduce to two relations on one unitary, and exact ones in a hyperfinite algebra exist only if F is amenable
distinct_from:
  thompson-f-hyperlinear-iff-relator-system-hs-unstable: that is the two-generator HS form in matrix algebras; this is a one-unitary form in which the endomorphism supplies the second generator, and it records what exactness costs.
  thompson-f-germ-local-hs-models-almost-commute: that kills models with a germ-local dyadic frame; tensor-shift models carry no such frame, and this is the separate verdict for them.
  half-space-tail-no-go: that is the tail no-go for groups with nontrivial intersection of compressor images; for F that intersection is trivial, so the tail argument says nothing, and this uses injectivity of the generated algebra instead.
  thompson-f-is-lea-only-if-amenable: that is the collapse of LEA to amenability through group-level local embeddings; this is the analogous collapse for exact operator-level models inside hyperfinite algebras.
artifacts:
  - experiments/thompson-f-shift-covariant-2026-09-17/search.py
  - experiments/thompson-f-shift-covariant-2026-09-17/results.txt
---

**ESTABLISHED (unreviewed).** Let `F = <x_0, x_1 | [x_0 x_1^-1, x_0^-1 x_1 x_0], [x_0 x_1^-1, x_0^-2 x_1 x_0^2]>`.
Let `(M, tau)` be a tracial von Neumann algebra with a faithful normal trace and a unital
trace-preserving `*`-endomorphism `sigma`. Call a unitary `a in M` a *shift-covariant model* if

```text
(A)  a* sigma(a) a   = sigma^2(a),
(B)  a* sigma^2(a) a = sigma^3(a).
```

1. **Reduction.** Every shift-covariant model defines a homomorphism `pi : F -> U(M)`, with
   `x_0 -> a` and `x_1 -> sigma(a)`, and `pi(x_n) = sigma^n(a)` for `n >= 1`. It is injective iff
   `a sigma(a) != sigma(a) a`. In `L(F)` the pair `a = lambda(x_0)`, `sigma = phi_*` is a model, where
   `phi` is the shift `x_i -> x_(i+1)`.
2. **Exact models see the regular trace.** If `pi` is injective, then `L(F)` is isomorphic to a
   direct summand `pi(F)'' z` of `pi(F)'' ⊆ M`, for a central projection `z`.
3. **Amenability collapse.** Some trace-preserving endomorphism of the hyperfinite `II_1` factor `R`
   carries a non-commuting exact model iff `F` is amenable. More generally, a non-commuting exact model
   in any injective `(M, tau)` forces `F` to be amenable.
4. **Local Bernoulli models are scalar.** Let `M = ⊗_(k>=0) M_d` with the one-sided Bernoulli shift, and
   let `A_[p,q)` be the sites `p..q-1`. If a unitary `a in A_[0,L)` satisfies (A), then `a` is a scalar.
   The 2-norm version: if `||a* sigma(a) a - sigma^2(a)||_2 <= delta`, then
   `||a - E_[0,L-1)(a)||_2 <= delta` and `||[a, sigma(a)]||_2 <= (5^(L-1) - 1) delta`. So a non-commuting
   approximate model with commutator at least `c` and defect `delta` needs support `L >= 1 + log_5(1 + c/delta)`.
5. **Sufficient route.** In the Bernoulli algebra of item 4, suppose unitaries `a_n in A_[0,L_n)` satisfy
   (A) and (B) within `delta_n -> 0` in `||.||_2`, and `||[a_n, sigma(a_n)]||_2 >= c > 0`. Then `F` is
   hyperlinear. Indeed `(a_n, sigma(a_n))` are matrices in `M_(d^(L_n+4))` satisfying both relators within
   `10 delta_n`.

**What this settles.** Tensor-shift and QCA-type constructions of hyperlinear models of `F` cannot be
exact. By item 3 an exact one proves amenability. By item 4 a finitely supported one in the Bernoulli
algebra is trivial. A certificate of this shape must be a genuinely approximate family, that is, an exact
non-commuting model in an ultrapower such as `(R^omega, sigma^omega)`. The invariant is injectivity of
`pi(F)''`, and every exact model in a hyperfinite host dies at item 2.

**Left open.** Can Bernoulli-local approximate models `a_n in A_[0,L_n)` stay non-commuting as
`delta_n -> 0`? By item 5 a positive answer proves `thompson-f-is-hyperlinear`. By item 4 the support must grow at least logarithmically in
`1/delta_n`. Each site peeled off costs a factor of 5, so item 4 gives no bound uniform in `L`. A
uniform bound `||[a, sigma a]||_2 <= C delta` would kill the class. A numerical probe of qubit models with `L = 2, 3` is in
`experiments/thompson-f-shift-covariant-2026-09-17/results.txt`. Its best models have
`||[a, sigma a]||_2` about `defect^2 / 2`, but these minima are not certified.

Derivation: `thompson-f-exact-shift-covariant-models-force-amenability-proof`.
