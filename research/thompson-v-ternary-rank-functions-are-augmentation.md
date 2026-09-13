---
rg: 2
id: thompson-v-ternary-rank-functions-are-augmentation
kind: claim
title: Every Sylvester rank function on the ternary group algebra of Thompson's V is the augmentation rank
refuted_by:
  - thompson-v-carries-ternary-nonaugmentation-rank-function
  - thompson-v-is-sofic
distinct_from:
  thompson-v-has-no-nontrivial-f2-rank-model: that is triviality of matricial characteristic-two rank models of V; this is the abstract Sylvester statement over F_3, which is the form the ternary counterexample chain consumes.
  sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one: that is the gate for the whole ternary unit group, which this implies through the signed Thompson group; the converse is not known, since a rank function on F_3[V] need not extend to the unit group.
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/signed-thompson-minus-one-gate-is-v-rank-gate-2026-09-12.md
---

**OPEN.** Every Sylvester matrix rank function on `F_3[V]` has `rk(1 - [g]) = 0` for all `g in V`, so it is
the augmentation rank.

**Why it matters.**
- **The signed group.** By `signed-thompson-z-moving-rank-functions-match-v-rank-functions`, this is exactly
  the statement that every Sylvester rank function on `F_3[E ⋊ V]` kills `1 - [z]`.
- **The unit group.** It implies `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one` (route
  `ternary-units-kill-minus-one-via-thompson-v-augmentation`). With the state upgrade, that gives the ternary
  counterexample chain.
- **Soficity.** It makes `V` not sofic and not `F_3`-linear sofic, because a sofic approximation gives a
  detecting rank function. So it is at least as hard as the soficity problem for `V`.

## Attempts

- **Subgroup reduction** (w5-c3-signed-thompson, artifact Sections 1–4). The `E ⋊ V` route to the
  characteristic-three gate lands here: `E ⋊ V` embeds in `V` as the centralizer of the first-letter swap
  `σ_0`, which is the image of `z`, and restriction to the unsigned `V` goes back. Where it stops: no proof;
  any proof settles soficity of `V` negatively.
- **Verified laws are consequences, not obstructions.** The Haar law on the signed diagonal, the lifted-trace
  law on finite subgroups, uniform displacement and the trivial-plus-regular torsion law are theorems about
  every model. A contradiction drawn from them on `E ⋊ V` would be a proof of this claim. None is known.
- **Tools that may transfer from characteristic two** (my reading, not re-derived; for `w4-upg-audit`). The
  covariance obstruction (`thompson-v-cantor-system-has-no-covariant-rank-model`), uniform displacement and
  the torsion law appear to use only additivity on orthogonal idempotents, subadditivity and conjugation
  invariance, so they likely hold for abstract rank functions over `F_3`. The symmetric-group stage theorem is
  matricial.
- **What a proof needs.** Relations among infinite-order, depth-changing elements, or among two finite
  subgroups generating an infinite subgroup (`v-rank-models-are-trivial-plus-free-on-odd-cycle-trees`,
  artifact Proposition 2.1: finite data never force triviality).

- **Audit for abstract rank functions** (w5-v-infinite-order, artifact
  `research/artifacts/thompson-v-rank-models-fixed-rank-and-wandering-freeness-2026-09-12.md`, Section 3.1).
  - **Holds abstractly:** the torsion law and uniform displacement. They use only unit invariance, subadditivity,
    additivity on orthogonal idempotents, Fourier inversion and group theory, so they hold for every Sylvester rank
    function on `F_3[V]` (the torsion law with `p = 5`).
  - **Holds but vacuous here:** the covariance theorem holds abstractly, but needs covariant cylinder idempotents
    in the target, so it says nothing on `F_3[V]` alone.
  - **[matricial]:** the covariance finite form, its truncation bound, and the symmetric-group stage theorem.
- **Reformulation** (`v-rank-torsion-constant-equals-global-fixed-rank`).
  - **Equivalence:** this claim is equivalent to `a_5(rk) = phi_V(rk) = 1` for every rank function on `F_3[V]`.
  - **What any other rank function looks like:** `phi_V < 1`, regular odd torsion on the part that is not fixed,
    and free wandering elements (`v-rank-models-act-freely-by-wandering-elements`).
  - **Matricial only:** the compression to a reduced model has no abstract version yet.
  - **Where it dies:** amenable configurations are inert (artifact Section 3.2).
- **Two firewalls** (w5-v-nonamenable; artifact
  `research/artifacts/thompson-v-rank-gate-sofic-and-characteristic-firewalls-2026-09-12.md`).
  - **Sofic configurations are inert** (`sofic-configurations-cannot-force-v-rank-triviality`).
    - **Construction:** for every sofic `K <= V`, ultraproduct permutation-module ranks give
      `rk(1 - [g]) = 1 - 1/ord(g)` on `F_3[K]`.
    - **What they satisfy:** every premise of an argument confined to `K`: the axioms, identities in `F_3[K]`, and
      single-element `V`-conjugacy with any conjugator.
    - **Consequence:** no such argument can even lower `rk(1 - [g])` below the sofic value.
    - **Covered:** lamp groups `<x, L> ≅ L wr Z`, free products of finite groups, and all of `F` if `F` is amenable.
      No Elek–Szabó import is needed.
  - **Characteristic-uniform arguments are inert** (`char-uniform-identities-cannot-force-v-rank-triviality`).
    - **Why:** the von Neumann rank on `C[V]` satisfies every argument whose identities already hold over a subring
      of `C`.
    - **Consequence:** a proof over `F_3` must use a `3`-sensitive identity, such as `(1 - [s])^3 = 0` for `s` of
      order `3`.
    - **The established abstract tools** (torsion law, fixed rank, displacement, wandering freeness) are satisfied
      by `rk_vN`, so none of them can be the decisive step.
  - **Where it dies.** A proof must combine two things:
    - a configuration not known to be sofic, or tuple-level conjugacy through conjugators outside it;
    - `3`-torsion.
  - **First live configuration:** `<x_0, x_1, s>` with `s` a clopen `3`-cycle, or the order-`3` Lochak–Schneps
    generator of `T` (not re-read).
  - **Open `p`-sensitive structure question:** `v-rank-order-char-cycles-are-trivial-plus-regular`.
- **Torsion is spent in characteristic 3; the gate stays OPEN at `<x_0, x_1, s>`** (w7-v-cycle-c3; artifact
  `research/artifacts/p-cycle-tree-rank-models-and-ternary-gate-2026-09-12.md`). Section 3 PASSed `w3-vf-linear`
  §33.4. The gate stays OPEN.
  - **Finite subgroups.** By the ESTABLISHED `v-rank-functions-are-trivial-plus-regular-on-cylinder-groups`
    (w7-v-cycle-c2), every rank function on `F_3[V]` is `phi_V rk_aug + (1 - phi_V) rk_reg` on every locally finite
    subgroup. Clopen 3-cycles get `rk((1 - [s])^j) = (1 - phi_V)(3 - j)/3`. Artifact Section 1 is a second derivation
    with different parameters.
  - **No intermediate target.** By convexity (w7-v-cycle-c2's artifact, Section 4.4), this claim is equivalent to
    `phi_V in {0, 1}` for every abstract rank function. Whether the law plus `x_0`, `x_1` conjugation forces
    `phi_V in {0, 1}` is the gate itself.
  - **Elementary abelian 3-subgroup data can't force the law** (`p-cycle-tree-invariance-cannot-force-order-char-law`,
    scoped by `w3-vf-linear` §33.3).
    - **The counter-model.** `rk_2` on `F_3[E_infinity]`, `[g] -> 1 + lambda(g) u` modulo `u^2`, is invariant under
      every injective endomorphism. It has `rk(1 - [g]) = 1/2` and `rk((1 - [g])^2) = 0`, which the law rules out.
    - **First premise broken.** Its induced extension to `E_3 ⋊ <s>` breaks single-element `V`-conjugacy. Data at
      `E_3 ⋊ <s>` together with `s ~ tau_1` is not covered.
  - **Inert.** The finite-subgroup formula holds for the augmentation rank and, on each sofic configuration, for the
    sofic ranks with `phi_V = 0`. So by `sofic-configurations-cannot-force-v-rank-triviality` it can't decide the
    gate.
  - **Where it stops.** I found no identity at `<x_0, x_1, s>` that mixes infinite-order elements with 3-torsion
    beyond single polynomials in `[x]` and matrices over locally finite subgroups. I found no non-augmentation rank
    function. Open:
    - **Abstract reduced quotient.** Is `(rk - phi_V rk_aug)/(1 - phi_V)` always a rank function? If so, the gate is
      equivalent to: no rank function on `F_3[V]` has `phi_V = 0`.
    - **Joint data** on `F_3[B ⋊ <x>]` and `F_3[<x_0, x_1, s>]`.

*Verification by `w3-vf-linear` (2026-09-12), §33.4 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS on the w7-v-cycle-c3 entry: convexity via [FR] Corollary 1.3(3), the locally finite formula and inertness all re-derive. Scope: "The law needs a prime other than 3" is proved only for elementary abelian 3-group data (§33.3). The cylinder-group node is now ESTABLISHED, not a candidate. The gate stays OPEN.*

- **Joint configuration: the models break on mixed-prime finite groups; the gate stays OPEN** (w7-v-gate-c3;
  artifact `research/artifacts/ternary-v-gate-joint-configuration-2026-09-12.md`). Sections 1–3 PASSed `w3-vf-linear`
  §34, partially: the [CFP] and [VX] inputs are taken as cited. Its wording fixes are applied. The gate stays OPEN.
  - **Which relation breaks the models** (artifact §1).
    - `rk_2` (profile `(1/2, 0)`) and `rk_3` (joint fixed rank `1/3` on every `E_r`) have no extension to `F_3[V]`.
    - Neither does `w7-v-cycle-c2`'s `1 + lambda_i e_12` model in characteristic 2.
    - In each case the first relation that no extension satisfies is the established Theorem 1.1 on a finite group
      `B ⋊ G`, where `B` is a clopen `q`-cycle group with `q != p` (5, or 3 in characteristic 2). This uses disjoint
      commutation, the conjugation data `g c_v g^(-1) = c_(g v)`, and the torsion law.
    - At fixed `q` the group is finite through the second derivation's `k` cycles per piece. For `rk_2`, `k = 3` is
      enough.
    - No `x_0`/`x_1` word and no lamplighter is needed. Mixtures of `rk_aug` with sofic ranks satisfy the same
      relations, so this decides nothing.
    - Not decided: whether 3-group data plus single-element `V`-conjugacy break every extension of `rk_2`.
  - **Generation** (artifact §2.1). `<x_0, x_1, s>` is proper in two cases:
    - if `s` fixes `0^∞` or `1^∞`, because `F` fixes both;
    - for `s = C`, the Cannon–Floyd–Parry order-3 generator (a product of two disjoint clopen 3-cycles), it is `T`.
    - Not decided for `s` not in `T` moving both endpoints.
    - `T` contains no clopen 3-cycle, since a nontrivial finite-order circle homeomorphism has no fixed point.
    - The gate question is unaffected: Theorem 1.1 is global, and `T` and `<x_0, x_1, s>` are not known to be sofic.
  - **Where it stops** (artifact §2.2–2.3).
    - No 3-sensitive matrix identity over `F_3[T]` or `F_3[<x_0, x_1, s>]` escapes the excluded list: locally finite,
      `B ⋊ <x>`, lamp groups, free products of finite groups, subrings of `C`.
    - No `phi_V = 0` characteristic-three model other than from soficity.
    - If `v-rank-functions-split-as-augmentation-plus-reduced` holds (w7-v-rank-split, OPEN), this claim is equivalent
      to: no rank function on `F_3[V]` has `phi_V = 0`.
  - **Summand node** (artifact §3). A `phi_V < 1` rank function refutes this claim and gives a faithful weakly finite
    image of `V`.
    - Pulled back to `E ⋊ V`, it shows that a proof of `ternary-anti-central-summand-has-no-weakly-finite-image`
      confined to `E ⋊ V` proves this claim.
    - It does not touch the summand node without `v-detecting-rank-functions-extend-to-ternary-leavitt-units`.
  - **Next lead.** `T = <x_0, x_1, C>` with `C` a product of two disjoint clopen 3-cycles. Look for a matrix over
    `F_3[T]` whose rank is forced both through `(1 - [C])^3 = 0` and through the wandering bound on `x_0`.

*Verification by `w3-vf-linear` (2026-09-12), §34 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: partial on w7-v-gate-c3 f5b2406fa, Sections 1–3 re-derived except the cited [CFP] and [VX] inputs. Claims 1.1–1.2, the Section 1.3 computation, Claim 2.1 and Claims 3.1–3.3 PASS. Fix: `C` covers `X`, so it is a product of two disjoint clopen 3-cycles, not a clopen 3-cycle, and `T` contains no clopen 3-cycle. The gate stays OPEN.*

*Verification by `w3-vf-linear` (2026-09-12), §34.7 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS on the w7-v-gate-c3 fix application 71434d4009. Fixes 1–2 and notes 1–5 of §34 are applied. The new bullet re-derives: given the OPEN `v-rank-functions-split-as-augmentation-plus-reduced`, the gate is equivalent to no rank function on `F_3[V]` with `phi_V = 0`. The §34 partial verdict stands, and the gate stays OPEN.*
