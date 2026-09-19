---
rg: 2
id: bilateral-lift-at-coordinate-projection-is-mirror-cocycle-lift
kind: claim
title: A class-bijective lift of the Jacobson Haar relation into the bilateral Laurent relation along the coordinate projection exists iff the symbol cocycle lifts to a measurable cocycle into the mirror normalizer E_- [T_-], so the bilateral route to soficity of EL_n(J) is exactly the vanishing of one pulled-back nonabelian 2-class, and it can never be realized by a point-independent (homomorphic) lift
distinct_from:
  jacobson-haar-relation-is-laurent-affine-restriction: that identifies R_E with the restricted one-sided Laurent affine relation and reduces soficity to it; this is about lifting R_E class-bijectively into the two-sided (bilateral) relation over F_2^(Z x n) along the coordinate projection, and proves that such a lift is equivalent to a mirror cocycle lift.
  jacobson-haar-relation-is-kazhdan-and-unsplittable: that kills treeing and ergodic-amalgam routes by property (T); this concerns a different route (class-bijective lift into a sofic bilateral relation), which property (T) does not obstruct, and turns its prerequisite into an exact equivalent.
  jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group: that is the group-level presentation E = P / L_- with P the fibre product of the two Toeplitz halves; this is the measured-relation form, where the fibre product is replaced by the extension 1 -> [T_-] -> N_- -> Q -> 1 and a group section is replaced by a cocycle section along the symbol cocycle.
artifacts:
  - research/bilateral-lift-at-coordinate-projection-proof.md
---

**ESTABLISHED** (route `bilateral-lift-at-coordinate-projection-proof`, swarm-0917-w15-w15-nh-break, 2026-09-19,
unreviewed). Role: belief-breaker, decomposition lane of `non-hyperlinear-group`.

**Context.** swarm-0917-w15-w15-nh-pull (worktree result, not yet landed at the time of writing) proposed the
following route to soficity of `EL_n(J)`.
* The bilateral Laurent affine relation `R'` is sofic.
* A class-bijective lift `(BL_N)` of the Haar relation `R_n` into `R'_N` would make `EL_n(J)` sofic and `L(R_n)` CE.
* A sufficient condition `(ML)` gives `(BL_n)`: a measurable cocycle into the mirror group `N_-` lifting the symbol.

This note proves that at the canonical placement `(ML)` is also **necessary**.

It also shows that a point-independent (homomorphic) version of `(ML)` would make `E` LEF. That part is conditional
on an unlanded non-LEF lemma.

**Setup.** Notation as in `jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group`, with `n >= 3`.
* `W = F_2^(Z x {1..n})` (finitely supported) is split as `W = V_- (+) V_+`. `X = Hom(W, F_2) = X_- x X_+`, where
  `X_+- = Hom(V_+-, F_2)`, has Haar measure `mu = mu_- x mu_+`.
* `V_fin^+-` is the finitely supported part of `X_+-`, identified with `V_+-` through the standard pairing.
* `G = W x| SL_n(A)` acts on `X` by `(w, g).xi = xi o g^(-1) + w`. This action is free and p.m.p.
  `R'` is its orbit relation, the bilateral Laurent affine relation.
* `Ê_+-` is the group of operators `xi -> xi o h^(-1)` on `X_+-` with `h in E_+-`. Every such operator is a finite-band
  Toeplitz matrix plus a finite matrix.
* `sigma(M) in M_n(A)` is its **Laurent part**: the symbol read off in the bilateral index, so that both diagonal
  blocks of the dual of one `g in SL_n(A)` have the same `sigma`.
* `R_n` is the orbit relation of `Ê_+` on `X_+`. This is the Haar relation `R_E` of `E = EL_n(J)`.
* The **symbol cocycle** is `s(x, y) = sigma(M)` for any `M in Ê_+` with `Mx = y`. It is well defined a.e. by Lemma 1.
* `T_-` is the tail relation on `X_-`, where `x ~ y` iff `x - y in V_fin^-`. `[T_-]` is its full group.
* `N_- = Ê_- [T_-] <= Aut(X_-, mu_-)`, with `pi_-(f t) = sigma(f)`.

**Definitions.**
* **(BL_n at the coordinate projection.)** There is a Borel subrelation `S <= R'` such that, off a null set, the
  projection `pr_+ : X -> X_+` maps every `S`-class bijectively onto an `R_n`-class.
* **(ML.)** There is a measurable cocycle `beta : R_n -> N_-` with `pi_- o beta = s` a.e.

**Theorem.**
1. **(Lemma 1, null-coset lemma.)** If `M` is a finite-band Toeplitz-plus-finite matrix on `X_+-` with `sigma(M) != 0`,
   then `{x : Mx in V_fin}` is `mu`-null. Consequences:
   * `Ê_- ∩ [T_-] = ker(sigma|_(Ê_-)) = L_-`, the finitary group, so `pi_- : N_- -> Q` is a well-defined
     homomorphism;
   * `1 -> [T_-] -> N_- -> Q -> 1` is exact, where `Q = sigma(Ê_-)`;
   * the symbol cocycle `s` is well defined.
2. **(Equivalence.)** `(BL_n at pr_+)` holds **if and only if** `(ML)` holds.
   * The `S` given by `beta` is `(x_-, x_+) ~ (beta(x_+, y_+) x_-, y_+)`.
   * Conversely, every `S` has this form for a unique `beta` (up to null sets): `beta(x_+, y_+)` is the fibre map of
     `S` over the pair `(x_+, y_+)`.
3. **(Cohomological form.)** `(BL_n at pr_+)` holds iff the Q-valued cocycle `s` lifts through the extension
   `1 -> [T_-] -> N_- -> Q -> 1`, where the lift is a cocycle and not a group section.
   * This is the lifting statement written `s^*[N_-] = 0`: the pull-back of the mirror extension along the symbol
     cocycle is trivial.
   * Concretely, fix a set-theoretic section `q -> f_q` of `sigma : Ê_- -> Q` and put `beta_0(x,y) = f_(s(x,y))`.
     Use the cocycle convention `beta(x,z) = beta(y,z) beta(x,y)`.
   * The defect `c(x,y,z) = beta_0(y,z) beta_0(x,y) beta_0(x,z)^(-1)` is `L_-`-valued. It is the Toeplitz 2-cocycle
     of the section, evaluated along `s`.
   * `(ML)` says that `c` is a coboundary in the nonabelian sense: there is a measurable `t : R_n -> [T_-]` with
     `beta_0 t` a cocycle.
4. **(No homomorphic lift, conditional.)** Suppose `beta` could be chosen of the form `beta(x, Mx) = tau(M)` for a
   homomorphism `tau : Ê_+ -> Ê_-` with `sigma o tau = sigma`. Then `M -> (M, tau(M))` embeds `E` in the LEF group `P` of
   `jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group`, so `E` would be LEF.
   * Since `EL_3(J)` is not LEF (swarm-0917-w14-w14-ptl-pull, unlanded), every `(ML)` witness must use `[T_-]`
     beyond `L_-`: the lift has to depend on the point.
   * This part is conditional on that lemma, and it is **not** part of the ESTABLISHED statement.

**What changes.**
* The single open prerequisite of the bilateral route ((BL_N), swarm-0917-w15-w15-nh-pull) is, at `N = n` and
  `r = pr_+`, **exactly** the lifting problem `(ML)`. It is not merely implied by it.
* So "the defect 2-cocycle is a `[T_-]`-coboundary", posed by w15-nh-pull as its next step, is not one way among
  several to reach `(BL_n)` at the canonical placement. It is the only way.
* A refutation of `(ML)`, for instance an invariant of `[T_-]`-valued cocycles over the Kazhdan relation `R_n` that
  the class `s^*[N_-]` fails, kills the canonical bilateral lift outright.
* Any surviving bilateral route has to use `N > n` or a projection `r` other than `pr_+`.

**Not covered.** Placements `r != pr_+`, amplifications `N > n`, and the truth of `(ML)` itself.

Proof: [[bilateral-lift-at-coordinate-projection-proof]].
