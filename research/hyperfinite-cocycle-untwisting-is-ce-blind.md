---
rg: 2
id: hyperfinite-cocycle-untwisting-is-ce-blind
kind: claim
title: Untwisting a free cocycle action of a Kazhdan group on R with U(R) coefficients is blind to Connes embeddability, and with U(R' ∩ R^omega) coefficients it is the CE question itself, so the Popa vanishing-cohomology test is not a decomposition of the Toeplitz corner
distinct_from:
  finitary-extension-ce-iff-action-lifts-to-normalizer: that is the lifting criterion for genuine actions; this proves the cocycle-action version (K3), the amplification identity (K2), and the CE-blindness of U(R) coefficients (K1), and applies them to the Toeplitz corner cocycle of EL_20(J).
  popa-vanishing-cohomology-amplification-and-ce-imports: that imports Popa's statements; this combines them into a counterexample on the Kazhdan group EL_20(F_2[x,x^(-1)]) and kills the Popa decision point of the Toeplitz corner.
  jacobson-symbol-sequence-does-not-virtually-split: that excludes untwisting at the group level by a Fredholm index; this is about untwisting the von Neumann cocycle omega with unitary coefficients, which that index does not see.
  leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity: that reduces the Toeplitz survivor class to hyperlinearity of EL_20(J); this shows that one of the two recorded decision points for that hyperlinearity carries no information in the direction of the goal.
---

**ESTABLISHED** by `hyperfinite-cocycle-untwisting-is-ce-blind-proof`.

**Conventions.** `R` is the hyperfinite `II_1` factor, `omega` a free ultrafilter, `R <= R^omega` the constant
sequences, `R_omega = R' ∩ R^omega`, and `N_(R^omega)(R)` the normalizer. Cocycle actions `(alpha, v)` are
normalized, crossed products `N x|_(alpha,v) Gamma` have canonical unitaries with `U_g x U_g^* = alpha_g(x)` and
`U_g U_h = v_(g,h) U_(gh)`, and "CE" means embeddable into `R^omega` (for groups, `L(Gamma)` is CE: Popa's
Definition 6.2 with [R06]). All of this is as in `popa-vanishing-cohomology-amplification-and-ce-imports`.

**(K2) Amplification commutes with crossed products.** Let `sigma` be a free action of `Gamma` on a `II_1` factor
`N`, `M = N x|_sigma Gamma`, `p in N` a projection, and `(sigma^p, v^p)` the amplification of Popa's
Definition 3.1. Then `pMp ≅ pNp x|_(sigma^p, v^p) Gamma`, by an isomorphism that is the identity on `pNp`.
Moreover a `II_1` factor is CE iff each (equivalently some) of its amplifications is.

**(K3) The cocycle form of Popa's Theorem 6.3.** Let `(alpha, v)` be a free cocycle action of a countable `Gamma`
on `R`. Then `R x|_(alpha,v) Gamma` is CE iff there are `V_g in N_(R^omega)(R)` with `Ad(V_g)|_R = alpha_g` and
`V_g V_h = v_(g,h) V_(gh)` for all `g, h`. No trace condition is needed. For `v = 1` this is Popa's 6.3.

**(K1) U(R)-untwisting is CE-blind on every sofic group with an infinite relative (T) subgroup.** Let `Gamma` be
such a group and `0 < t < 1`. Let `(sigma^t, v^t)` be the amplification by `t` of the noncommutative Bernoulli
action with base `R`. Then:
- `(sigma^t, v^t)` is a free cocycle action of `Gamma` on `R^t ≅ R` whose cocycle is **not weak-vanishing** in
  `U(R^t)`;
- its crossed product `≅ p L(S_inf wr Gamma) p` is **CE**;
- at `t = 1` the cocycle vanishes (the action is genuine) and the crossed product is again CE.

So neither vanishing nor weak vanishing of a free cocycle in `U(R)` is implied by CE of the crossed product. CE is
invariant under amplification. U(R)-vanishing is not.

**Application.** Let `E = EL_20(J)`, `J = F_2<S,T | TS=1>`, `L = GL_fin(V) = ker(E -> Q)` and
`Q = EL_20(F_2[x,x^(-1)])`. Then:
- **(A1) The corner cocycle is a free cocycle action on `R`.** `L(E) = R x|_(alpha,omega) Q`, with `R = L(L) ≅ R`
  and `(alpha, omega)` free.
- **(A2) `Q` meets (K1).** `Q` is residually finite, hence sofic, and has property (T). So `Q ∉ VC_w(R)`, and
  `Q` carries the CE-blind cocycle actions of (K1).
- **(A3) The kill.** The Popa vanishing-cohomology decision point of `agent-leavitt-not-bcs-negative-root-corner`
  (its entries at the Jacobson reduction, the mirror-head swap and the virtual-splitting index) contributes no
  independent prerequisite to `non-hyperlinear-group`:
  - *U(R) coefficients, negative outcome.* A proof that `omega` is not a (weak) coboundary in `U(R)` does not
    imply that `E` is non-hyperlinear. Any implication "free cocycle action of `Q` on `R` with non-weak-vanishing
    cocycle ⇒ crossed product not CE" is false, by (K1) applied to `Q` itself. An argument from this outcome must
    therefore use an additional property of `(alpha, omega)` that fails for `(sigma^t, v^t)`, and that property,
    not the non-vanishing, carries the proof.
  - *U(R) coefficients, positive outcome.* If `omega` weakly vanishes in `U(R)`, then `L(E)` is the crossed
    product of a genuine free action of `Q` on `R`, twisted at most by a scalar 2-cocycle. By (K3) its CE is again
    equivalent to a normalizer lift. This is the same question with a trivial cocycle, not a smaller one. This
    outcome can only feed the refutation side of the goal, and even there it decides nothing by itself.
  - *`U(R_omega)` coefficients.* By (K3), "the induced cocycle vanishes in `R' ∩ R^omega`" is equivalent to `E`
    being hyperlinear, so it is a restatement of the hole, not a prerequisite of it.
- **Invariant.** Invariance under amplification `(alpha, v) -> (alpha^t, v^t)`. CE of the crossed product has it
  (K2). Vanishing in `U(R)` does not have it (K1).
- **Step where every member dies.** The passage from `U(R)` to `U(R_omega)` coefficients, i.e. (K3). The
  amplified Bernoulli cocycles are exactly the ones that do not untwist in `U(R)` but do untwist in `U(R_omega)`.

**Not claimed.** Nothing here decides whether `E` is hyperlinear, or whether `omega` is a coboundary in `U(R)`.
The recorded wall-rigid decision point for approximations of `P` is untouched.

**Sufficient condition for the refutation side (recorded, not proved).** Let `beta` be the genuine action of `Q`
on `R_bi = L(GL_fin(W))` from `untwisted-bilateral-symbol-enrichment-is-lef`. Suppose `(alpha, omega)` is cocycle
conjugate, up to an automorphism of `Q`, to an amplification `beta^t`. Then (K2), Popa's Proposition 1.2 and CE
of `L(H_bi)` (from LEF) give that `E` is hyperlinear. Whether the Toeplitz corner is such an amplification is open.
It does not follow from the group-level compression `V -> V_+`, which embeds `L(L)` in `R_bi` as a subalgebra and
not as a corner `p R_bi p`.
