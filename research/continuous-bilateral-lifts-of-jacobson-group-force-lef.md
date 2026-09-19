---
rg: 2
id: continuous-bilateral-lifts-of-jacobson-group-force-lef
kind: claim
title: The topological full group of the bilateral Laurent affine action is LEF, so no bilateral lift of EL_n(J) with n >= 4 into the orbit relation of any rank can be continuous; every surviving bilateral or mirror-cocycle lift is genuinely measurable
distinct_from:
  zd-subshift-full-group-lef-via-periodic-relator-shifts: that treats Z^d acting by shifts on a subshift; this treats the non-amenable affine group A^N x| SL_N(A) acting algebraically on the full compact group (F_2^Z)^N, where periodic points are an invariant submodule and the finite models come from reducing A mod z^m - 1, and applies the result to Jacobson lifts.
  full-shift-topological-full-group-is-residually-finite: that is about the Z-action by the shift; here the acting group is W x| SL_N(A), whose elements do not preserve finite orbits, so only LEF (not residual finiteness) is obtained, by periodizing translation parts.
  untwisted-bilateral-symbol-enrichment-is-lef: that proves LEF of the abstract group L x| Q by folding coordinates; this proves LEF of a topological full group of an action on a compact space and uses it to classify which lifts of E into full groups can exist.
  aperiodic-full-groups-lift-along-factor-maps: that lifts topological full groups along factor maps of Cantor systems; this shows the reverse phenomenon at the Jacobson corner, that a lift of E along the coordinate projection can never be topological.
  jacobson-el3-lef-from-local-mirror-lifts: that kills spatial global mirror sections of P -> E by the commuting-pair index; this kills continuous measured lifts into the bilateral orbit relation, at every rank N and every placement, by LEF, and leaves the index-free measurable lifts.
  cohn-elementary-group-is-not-lef: that is the imported input (EL_n(J) not LEF for n >= 4); this converts it into a statement about the regularity of every bilateral lift.
---

**ESTABLISHED** (route `continuous-bilateral-lifts-of-jacobson-group-force-lef-proof`). Parts (C1)–(C3) are
unconditional. (C4) at `n >= 4` uses `cohn-elementary-group-is-not-lef`. The case `n = 3` is **not** killed. There
(C4) becomes the positive implication (C5).

**Setting.**
- `A = F_2[z^(+-1)]` and `N >= 1`. `X_N = (F_2^Z)^N` is the compact group of all bi-infinite sequences. It is an
  `A`-module, with `z` acting as the shift. Its Haar measure `mu` is the uniform Bernoulli measure.
- `W = A^N` is the finitely supported part of `X_N`. `G_N = W x| SL_N(A)` acts on `X_N` by homeomorphisms,
  `(w, lambda) . xi = lambda xi + w`.
- `R'_N` is the orbit relation of this action.
  - `[R'_N]` is its measured full group: measure-preserving `a.e.` bijections `xi -> h(xi) . xi` with `h`
    measurable into `G_N`.
  - `[[G_N ~ X_N]]` is its topological full group: homeomorphisms `xi -> h(xi) . xi` with `h : X_N -> G_N`
    continuous. Because `G_N` is discrete and `X_N` is compact, such an `h` is locally constant with finitely many
    values.
- `J = F_2<S,T | TS = 1>`, `E_n = EL_n(J)` and `L = GL_fin`, as in `cohn-elementary-group-is-not-lef`.

**Theorem.**
- **(C1) Free points are comeagre and conull.** For `g != 1` in `G_N`, `Fix(g)` is a closed Haar-null set. Hence
  the cocycle `h` of an element of `[[G_N ~ X_N]]` is unique everywhere, and satisfies the cocycle identity
  `h_(phi psi)(xi) = h_phi(psi xi) h_psi(xi)` at every point.
- **(C2) Periodized models.** Let `Per_m = {xi : z^m xi = xi} ≅ (A/(z^m - 1))^N` and
  `per_m(w) = sum_k z^(km) w`. Then `pi_m(w, lambda) : xi -> lambda xi + per_m(w)` is a homomorphism
  `G_N -> Sym(Per_m)`. Set `Phi_m(phi)(xi) = pi_m(h_phi(xi)) xi` for `xi in Per_m`. For every finite
  `F ⊆ [[G_N ~ X_N]]` and every `m` larger than an explicit bound, the following hold:
  - `Phi_m` is injective on `F`;
  - `Phi_m(phi psi) = Phi_m(phi) Phi_m(psi)` for `phi, psi in F`.
- **(C3) LEF.** `[[G_N ~ X_N]]` is LEF for every `N`, and so is every subgroup of it.
- **(C4) Kill, n >= 4.** Let `n >= 4`, `N >= 1`, and let `alpha : E_n -> [R'_N]` be an injective homomorphism.
  Then for some `e` in any symmetric generating set `Sigma` of `E_n`, the cocycle `h_(alpha(e))` is not `a.e.`
  equal to any continuous (that is, locally constant) map `X_N -> G_N`.
  - Equivalently: no faithful action of `E_n` on `(X_N, mu)` by elements of `R'_N` has generators that agree
    `a.e.` with elements of `[[G_N ~ X_N]]`.
  - The rank `N` is arbitrary. So this holds at every placement `r` of the bilateral lift whose witness is an
    injective homomorphism into some `[R'_N]`.
- **(C5) The case n = 3.** If some `alpha : E_3 -> [R'_N]` is injective and its generators have `a.e.`
  locally constant cocycles, then `EL_3(J)` is LEF, hence sofic.

**Application to the bilateral / mirror-cocycle route.**
- **(ML) witnesses are faithful.** An (ML) witness at `pr_+` is an action
  `e~(xi) = sigma(e) xi + w_e(xi)` on `X_n` for which `pr_+` intertwines it with the defining action of `E` on
  `X_+ = (F_2^(Z>=0))^n`, the one-sided sequences. That defining action extends the
  action of `E` on `V`, is continuous, and is faithful. If `e~ = id` `a.e.`, then `e` acts trivially on a conull
  set of `X_+`, and hence, by continuity, on `V`. So `e = 1`.
  - Every (ML) or (BL_N at r) witness is therefore an injective `alpha : E_n -> [R'_N]`, and (C4) applies.
  - The plus part of `w_e` is forced by `pr_+`-equivariance and is locally constant: it is the finite-rank
    Toeplitz defect of `e`.
  - So (C4) says: **for n >= 4, the free minus part of every (ML) witness is discontinuous on a set of positive
    measure, for some generator.**
- **The class killed.** "Build the bilateral lift by a local rule." That means sliding-block or cellular
  corrections, finite-window mirror data, Toeplitz or Hankel formulas with finitely many cases, or any
  construction in which each generator's correction depends on finitely many coordinates. At `n >= 4` every such
  construction fails, at every rank `N` and every placement.
- **Invariant.** LEF.
- **Step where every member dies.** Periodization (C2). On `Per_m` the translation parts are replaced by their
  periodizations. That replacement is exact on every ball once `m` exceeds the window radius plus the support
  radius, so the relators of `E_n` become exact finite permutation relations.
- **Dividing line.**
  - Measurable: `E <= [R'_N]` gives soficity of `E`, whenever `R'_N` is sofic (Elek–Lippner). That soficity is
    shown in wave-15 work that has not landed, and it is not used here.
  - Topological: `E <= [[G_N ~ X_N]]` gives LEF.
  - Because of (C4), a proof of soficity for `n >= 4` along this route must exploit measure-theoretic
    discontinuity. It cannot pass through finite-window corrections.
- **Survivors.**
  1. Witnesses whose corrections are not `a.e.` locally constant. Examples: unbounded `w_e`, corrections defined
     through tail limits, or corrections that are measurable selections of `T_-` classes.
  2. At `n = 3`, continuous witnesses. Such a witness would prove LEF (C5). This is consistent with
     `jacobson-el3-lef-from-local-mirror-lifts`, which already requires rank-three-specific constructions.

**Not claimed.**
- Nothing here decides (ML), (BL_N), or the soficity of `EL_n(J)`.
- No statement is made about lifts whose cocycles are continuous only on a dense open conull set.

DERIVATION
continuous-bilateral-lifts-of-jacobson-group-force-lef-proof
