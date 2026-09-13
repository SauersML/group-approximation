---
rg: 2
id: thompson-v-has-no-nontrivial-f2-rank-model
kind: claim
title: Every homomorphism from Thompson's V into a characteristic-two rank ultraproduct is trivial
refuted_by:
  - thompson-v-is-f2-linear-sofic
distinct_from:
  leavitt-el3-rank-models-over-finite-fields-are-trivial: that is rank triviality for EL_3 over the Leavitt algebras in every characteristic; this is rank triviality for the subgroup V in characteristic two. By simplicity of the Leavitt units it implies the binary characteristic-two case of that claim, so it is at least as strong; the converse is not known, since no nontrivial rank model of V is known that fails to extend to the Leavitt units.
  thompson-v-cantor-system-has-no-covariant-rank-model: that excludes rank models carrying a covariant cylinder algebra; this excludes every rank model, covariant or not.
artifacts:
  - research/artifacts/thompson-v-rank-models-cantor-covariance-2026-09-12.md
---

**OPEN.** Let `M = prod_(k->omega) M_(n_k)(F) / N_rk` be a rank ultraproduct over a field `F` of
characteristic two. Then every group homomorphism `sigma : V -> M^x` is trivial.

**Why it matters** (artifact Section 4):
- **V is not F_2-linear sofic.** An `F_2`-linear sofic approximation of `V` gives an injective
  homomorphism into such an ultraproduct. This feeds `non-linear-sofic-group` through
  `non-linear-sofic-via-thompson-v-rank-triviality`.
- **The binary Leavitt units have only trivial char-2 rank models.** `V <= R^x = L_(F_2)(1,2)^x` by
  `leavitt-cylinder-swaps-generate-thompson-in-el`, and `R^x` is simple
  (`binary-leavitt-unit-group-is-simple`). So a nontrivial homomorphism from `R^x` is injective, and
  restricts to a nontrivial homomorphism of `V`. That is the binary, characteristic-two case of
  `leavitt-el3-rank-models-over-finite-fields-are-trivial`.
- **Scope.** The support filter `thompson-v-linear-witness-supports-kill-g-in-rank-models` depends on
  the characteristic. A nontrivial `F_2` rank model of `V` refutes only the binary target
  `thompson-v-order-three-averaging-idempotent-is-full`; the ternary swap target needs characteristic three.

## Attempts

- **Covariant models are dead.** `thompson-v-cantor-system-has-no-covariant-rank-model`: no model carries
  a covariant copy of the cylinder algebra, and finite-stage covariance defect is at least `1/4`.
- **Monomial models are sofic models.** `monomial-rank-models-are-hamming-models`. A monomial model
  would make `V` sofic, which is open (`thompson-v-is-sofic`). So a proof of this claim must also
  handle non-monomial models, and a counterexample must be non-monomial or settle soficity of `V`.
- **Involution displacement does not decide it.**
  - In characteristic two every cylinder swap `pi` has `N = pi - 1` with `N^2 = 0`.
  - Swaps whose union is not all of `X` form one conjugacy class. `pi_(a<->b) = pi_(a0<->b0) pi_(a1<->b1)`
    with commuting factors conjugate to `pi`, so `N = N_0 + N_1 + N_0 N_1`, and `rk N <= 2 rk N`.
  - Trivial-plus-free displacement data satisfy every such inequality, just as for the Leavitt roots
    (`dyadic-root-displacement-data-admit-trivial-plus-free-models`).
  - Calibrated dead end: conjugacy of `pi_(a0<->b0)` to `pi_(a<->b)`, commutation, `N^2 = 0` and equal
    displacement do not force `rk(N_0 N_1) = 0`. The regular Klein four-group in `Sym(4)` satisfies all
    of them with `N_0 N_1 != 0` (artifact 5.2). A proof must use the depth-changing elements of `V`.
- **3-cycle commutators give uniform displacement, not triviality.**
  - `thompson-v-rank-models-displace-every-element-uniformly`: every nontrivial element of `V`
    displaces at least `d_3/4`, where `d_3` is the displacement of a cylinder 3-cycle.
  - Honest representations of large symmetric groups satisfy the same inequality, so this is a
    necessary condition on a counterexample, not an obstruction.
  - At finite stages it kills more. `thompson-v-rank-models-through-displacing-sym-reps-are-trivial`
    shows that a model whose stages are symmetric-group representations with 3-cycle displacement
    bounded below is an exact local embedding, and none exists. So a counterexample built from finite
    symmetric groups must have displacement tending to zero, like the natural permutation module.
- **Verification.** `gk-vf-linear` passed the covariance obstruction independently (Section 50 of its
  verification artifact). `w3-vf-linear` has the request.
- **The root identity lives outside V.** Root elements `1 + E_ij` of `EL_3(R)` are not in `V`, so
  `rank-models-of-el3-satisfy-the-two-root-identities` does not specialize to `V`. This claim is the
  stronger target.
- **Torsion is spent** (`w4-gate-v2`; `v-rank-models-are-trivial-plus-free-on-odd-cycle-trees`; artifact
  `research/artifacts/thompson-v-rank-models-torsion-spectra-2026-09-12.md`).
  - **Structure.** On every odd clopen-cycle subgroup, a rank model is a fraction `a_p` of trivial plus a
    fraction `1 - a_p` of regular representation, with one global constant. The model is nontrivial iff
    `a_p < 1`.
  - **No finite shortcut.** By artifact Proposition 2.1, the trivial-plus-regular model of any finite
    subgroup meets every conjugacy constraint, in every characteristic. So a proof must use infinite-order
    elements, or two finite subgroups that generate an infinite subgroup.
  - **No halving from torsion.** Torsion averaging idempotents multiply over disjoint supports: the joint
    fixed rank is `a + (1 - a)/p^k`, and it never halves. The covariance obstruction needs support
    idempotents that add over a split, and none is known inside the image of `F[V]`.
  - **No power-conjugacy.** `y ~ y^2` would give `rk((y-1)^2) = rk(y-1)`, but that route is unavailable
    for `x_0`. Slopes at fixed points are conjugacy invariants, and `x_0^k` has slopes `+k` and `-k`
    (artifact Section 3).

- **Fixed rank and wandering freeness** (w5-v-infinite-order; artifact
  `research/artifacts/thompson-v-rank-models-fixed-rank-and-wandering-freeness-2026-09-12.md`).
  - **Proved** for abstract Sylvester rank functions in every characteristic, hence for models:
    - the torsion constant `a_p` equals the fixed rank `phi_V` (`v-rank-torsion-constant-equals-global-fixed-rank`);
    - every element with a wandering clopen, `x_0` included, has `rk q([x]) >= 1 - phi_V` for `q != 0`
      (`v-rank-models-act-freely-by-wandering-elements`).
  - **[matricial]** Every nontrivial model compresses to a nontrivial model with no fixed vectors. There torsion is
    regular and wandering elements are free.
  - **Where it dies.** That is sofic behaviour. The Følner rank functions of the amenable subgroups these arguments
    use satisfy all of it: lamps along wandering orbits, `BS(1,2)`-type partial conjugacies, locally finite torsion.
    With Elek–Szabó uniqueness (imported, artifact Section 3.2) they also satisfy `V`-conjugacy invariance on those
    subgroups. A proof needs relations in a non-amenable subgroup, and any proof shows `V` is not sofic.

- **Two firewalls** (w5-v-nonamenable; artifact
  `research/artifacts/thompson-v-rank-gate-sofic-and-characteristic-firewalls-2026-09-12.md`).
  - **Non-amenable is not enough; non-sofic is needed** (`sofic-configurations-cannot-force-v-rank-triviality`).
    - **Construction:** for every sofic `K <= V`, the ultraproduct permutation-module ranks have
      `rk(1 - [g]) = 1 - 1/ord(g)`.
    - **What they satisfy:** every premise of an argument confined to `K`, including single-element conjugacy
      through any conjugator.
    - **Consequence:** free products of finite groups, lamp groups `L wr Z`, and all of `F` if `F` is amenable are
      inert. No Elek–Szabó import is needed.
  - **Characteristic-uniform arguments are inert** (`char-uniform-identities-cannot-force-v-rank-triviality`).
    - **Why:** over `C`, the von Neumann rank satisfies every argument whose identities already hold over a subring
      of `C`.
    - **Consequence:** a proof over `F_2` must use a `2`-sensitive identity, such as `(1 + [t])^2 = 0` for an
      involution `t`. `(1 - u_t)^2 = 2(1 - u_t)` is not zero over `C`.
    - **The established abstract tools** can't be the decisive step.
  - **Where it dies.** A proof must combine two things:
    - a configuration not known to be sofic, or tuple-level conjugacy through outside conjugators;
    - `2`-torsion.
  - **First live configuration:** `<x_0, x_1, t>` with `t` a clopen transposition, or the order-`4` Lochak–Schneps
    generator of `T` (not re-read).
  - **Open:** `v-rank-order-char-cycles-are-trivial-plus-regular`, the characteristic-`2` law
    `rk(1 + [t]) = (1 - phi_V)/2` for a clopen transposition `t`, where `(1 + [t])^2 = 0`. The first version wrote
    `rk((1 + [t])^j) = (1 - phi_V)(2 - j)/2` for all `j`, which fails at `j = 0`. In characteristic `2` the relevant
    identity is `rk(x_1 + x_2) = rk(x_1)` for disjoint clopen transpositions whose supports leave a nonempty clopen
    complement. Then `x_1 + x_2 = [t_1](1 + [t_1 t_2])` with `t_1 t_2` conjugate to `t_1`.

- **Order-char law on all finite subgroups** (w7-v-cycle-c2; artifact
  `research/artifacts/thompson-v-rank-functions-regular-on-cylinder-groups-2026-09-12.md`). These are candidate
  proofs, held OPEN until `w3-vf-linear` re-derives them.
  - **Candidate theorem** (`v-rank-functions-are-trivial-plus-regular-on-cylinder-groups`). On every finite subgroup
    `G <= V`, in every characteristic, `rk(A) = phi_V rank_F eps(A) + (1 - phi_V) rank_F Reg(A)/|G|`. This proves
    the open item above: `rk(1 + [t]) = (1 - phi_V)/2`.
  - **Torsion is spent, 2-torsion included.**
    - On finite and locally finite subgroups, `phi_V` pins the rank function: augmentation mixed with
      permutation-module ranks.
    - So `(1 + [t])^2 = 0` is not decisive by itself (`sofic-configurations-cannot-force-v-rank-triviality`).
  - **The gate in terms of `phi_V`** (artifact Section 4.2).
    - **Local formula.** `phi_V = 1 - 2 rk(1 + sigma(t))`.
    - **Convexity.** Block sums with the trivial model reach every value of `phi_V` in `[phi_V(sigma), 1]`. So the
      gate is equivalent to `phi_V in {0, 1}` for every model. Whether the law plus `x_0`, `x_1`-conjugation forces
      that is the gate itself.
    - **Reduced models.** With [FR] Corollary 1.3(5) ([matricial]), the gate is equivalent to this: no model has
      `rk(1 + sigma(t)) = 1/2`. Equivalently, no model is regular on every finite subgroup.
  - **Invariance under disjoint-support endomorphisms doesn't prove the law** (artifact Section 3).
    - **Construction.** `rho(t_i) = 1 + lambda_i e_12` over `F_2(lambda_1, lambda_2, ...)` gives a rank function on
      `F_2[E_infinity]`.
    - **What it satisfies.** It is invariant under every injective endomorphism, and `rk(x_1 + x_2) = rk(x_1)`.
    - **Why it fails the law.** Its fixed rank is `1/2` at every level.
    - **First premise it breaks.** Odd cycles normalized by the 2-group.
  - **Where it dies.** A proof needs infinite-order elements in a configuration not known to be sofic, together with
    2-torsion. The first live configuration is still `<x_0, x_1, t>`.
