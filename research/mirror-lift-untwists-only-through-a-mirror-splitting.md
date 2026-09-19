---
rg: 2
id: mirror-lift-untwists-only-through-a-mirror-splitting
kind: claim
title: A mirror cocycle lift of the Jacobson Haar relation that untwists to a homomorphism is cohomologous to a homomorphic splitting of the mirror extension over Q, while on every treeable subrelation the lift always exists, so the bilateral route splits into a rigidity prerequisite and a group-splitting prerequisite
distinct_from:
  bilateral-lift-at-coordinate-projection-is-mirror-cocycle-lift: that proves (BL_n at pr_+) iff (ML) and that a lift of the form tau(M) with tau into E_- would make E LEF; this proves that any (ML) witness whose group cocycle is cohomologous to a homomorphism is [T_-]-cohomologous to rho o s for a homomorphic section rho of N_- -> Q (values in N_-, not E_-), and that (ML) holds on every treeable subrelation.
  jacobson-haar-relation-lifts-into-bilateral-relation: that is the open placement statement (BL_N); this decomposes its canonical case (N = n, r = pr_+) into two statements that can fail independently, and answers its proposed corner test (positively, hence uninformatively).
  jacobson-symbol-sequence-does-not-virtually-split: that refutes a section Q -> E by a Fredholm index; the splitting (HS) here takes values in N_- = E_- [T_-], where the index is not defined, so (HS) is the measurable relaxation of what that node refutes.
  treeable-free-actions-lift-across-finite-normal-extensions: that lifts free actions across finite extensions along a treeing; this uses the same edge-lifting device for a nonabelian cocycle lifting problem with an infinite Polish kernel [T_-] over a non-free action.
  hyperfinite-cocycle-untwisting-is-ce-blind: that is about untwisting a von Neumann 2-cocycle with unitary coefficients; this is about untwisting a measured-relation 1-cocycle with values in the Polish group N_-.
artifacts:
  - research/mirror-lift-untwists-only-through-a-mirror-splitting-proof.md
---

**ESTABLISHED** (route `mirror-lift-untwists-only-through-a-mirror-splitting-proof`, swarm-0917-w16-w16-nh-last1,
2026-09-19, unreviewed). All three parts are unconditional implications. Parts 2 and 3 do not assert (SR) or (HS).

**Setup.** Notation of `bilateral-lift-at-coordinate-projection-is-mirror-cocycle-lift`, with `n >= 3`.
* `Ê_+` acts on `(X_+, mu_+)`, with orbit relation `R_n` and symbol `sigma : Ê_+ -> Q = SL_n(A)`.
* `ker(sigma) = L_+` is the finitary group.
* `s : R_n -> Q` is the symbol cocycle.
* `N_- = Ê_- [T_-]`, with `pi_- : N_- -> Q`.
* Cocycle convention: `beta(x,z) = beta(y,z) beta(x,y)`.
* An (ML) witness `beta` has the group cocycle `alpha_beta(M, x) = beta(x, Mx)`.
  It satisfies `alpha(M'M, x) = alpha(M', Mx) alpha(M, x)`.

**Definitions.**
* **(HS)** There is a homomorphism `rho : Q -> N_-` with `pi_- o rho = id_Q`. That is, the mirror extension
  `1 -> [T_-] -> N_- -> Q -> 1` splits.
* **(SR)** Every measurable cocycle `alpha : Ê_+ x X_+ -> N_-` is cohomologous to a homomorphism. That is, there are
  a measurable `phi : X_+ -> N_-` and a homomorphism `rho' : Ê_+ -> N_-` with
  `alpha(M, x) = phi(Mx) rho'(M) phi(x)^(-1)` a.e.
* **(SR_beta)** The same, but only for the one cocycle `alpha_beta`.

**Theorem.**
1. **(N_- is a Polish group of finite type.)** In the uniform metric `d(f,g) = mu_-{f != g}`:
   * any two distinct cosets of `[T_-]` in `N_-` are at distance exactly 1;
   * `N_-` is closed in the full group `[R_-]` of the mirror Haar relation;
   * hence `N_-` is a closed subgroup of `U(L(R_-))`, so it lies in Popa's target class `U_fin`.

   So (SR) is a Popa-type cocycle superrigidity statement with an admissible target.
2. **(Untwisting forces a splitting.)** Let `beta` be an (ML) witness satisfying (SR_beta). Then (HS) holds.
   Moreover `beta` is `[T_-]`-cohomologous to `rho o s`: there is a measurable `psi : X_+ -> [T_-]` with
   `beta(x, y) = psi(y) rho(s(x,y)) psi(x)^(-1)` a.e.
   * Hence, under (SR), **(ML) iff (HS)**. The converse (HS) implies (ML) is `beta = rho o s`.
   * Two inputs are used. `Ê_+ ↷ X_+` is weakly mixing, which removes the `Q`-part of `phi`. Every element of `L_+`
     fixes a set of positive measure, which kills `rho'` on `L_+`.
3. **(Treeable subrelations never obstruct.)** Let `R_0 <= R_n` be a treeable Borel subrelation. Then `s|_(R_0)` lifts to
   a measurable cocycle `R_0 -> N_-`. In particular this holds when `R_0` is the orbit relation of an amenable
   subgroup `H <= Ê_+`, which is hyperfinite by Connes--Feldman--Weiss.
   * The corner test proposed on `jacobson-haar-relation-lifts-into-bilateral-relation` uses the subrelation generated
     by `x_12(S), x_12(T), x_23(S), x_23(T)`. These lie in the class-2 nilpotent group `UT_3(J)`.
   * So that test **always succeeds**: the mirror head `x_13(Q')` is always absorbed by a point-dependent `[T_-]`
     correction. The test cannot yield an obstruction.

**Decomposition of the canonical bilateral route.** The canonical case `N = n, r = pr_+` of `(BL_N)` is `(ML)`.
It now sits between two prerequisites, each able to fail independently.
* **(HS)**, a group-splitting problem. It implies (ML), hence `(BL_n)` and soficity of `EL_n(J)`.
  * Its point-independent restriction, with values in `Ê_-`, is refuted by `jacobson-symbol-sequence-does-not-virtually-split`
    (mirror form): commuting lifts of `(u_a, h^k)` do not exist in `Ê_-`.
  * So every (HS) witness uses `[T_-]` essentially.
* **(SR)**, a rigidity problem. It is not imported. Popa's theorem needs a malleable action (Bernoulli, Gaussian), and
  `Ê_+ ↷ X_+` is an algebraic action on the dual of the non-permutation module `V_+`.
  * The rigidity half is available: `R_n` is Kazhdan (`jacobson-haar-relation-is-kazhdan-and-unsplittable`).
  * The deformation half is what is missing.

Consequences:
* **Refuting (ML)** reduces to **(SR_beta) for every witness, plus not (HS)**. So a refutation must pass through a proof
  that the extension `N_- -> Q` does not split, with `[T_-]` allowed.
* **Proving (ML) without (HS)** requires a witness `beta` whose group cocycle is *not* cohomologous to any
  homomorphism. So the Kazhdan relation `R_n` must fail U_fin-cocycle superrigidity for that target.
* **Localization is useless** (part 3). Neither direction can be decided on a treeable or amenable piece of `R_n`.
  Any obstruction is carried by the non-treeable part of `R_n` as a whole.

**Next falsifiable step.** Decide (HS) for `n = 3` on the commuting pair `(u_a, h)` of the virtual non-splitting node.
Are there a measure-preserving involution `u' in u~[T_-]` and `h' in h~[T_-]` with `u'h' = h'u'`?
* A negative answer needs a measurable replacement for the Fredholm index of the image layer `im(u~+1)`.
* The natural candidate is the relative-entropy index `H(h' F | F) - H(F | h' F)` of the `u'`-invariant
  sigma-algebra `F`. It is recorded in the proof, Section 5, together with the exact step where it can fail: finiteness
  of the conditional entropies under unbounded `[T_-]` corrections.

Proof: [[mirror-lift-untwists-only-through-a-mirror-splitting-proof]].
