---
rg: 2
id: lifted-thompson-t-is-not-mf
kind: claim
title: "Every homomorphism from the lifted Thompson group T-bar to the unitary group of a norm matrix corona kills the central translation z"
distinct_from:
  lifted-thompson-t-mf-radical-dichotomy: that is the unconditional dichotomy Rad_MF(T-bar) in {1, T-bar}, which makes this one-word statement equivalent to full MF radical; this is the open non-MF branch.
  lifted-thompson-t-center-has-relative-t: that asks for every cnd function to be bounded on the centre, a Hilbert-space rigidity statement against the Haagerup property; this asks for every norm-corona representation to kill the centre, which is an approximation statement, and neither is known to imply the other.
  property-t-free-torsion-free-fp-non-mf-seed: that asks for some torsion-free finitely presented non-MF group; this names one candidate, which by the dichotomy would even have full radical.
---

**OPEN.**  Let `T̄` be the lift of Thompson's `T` to `R`, and let
`z(x) = x+1`.  Claim:

```text
z in Rad_MF(T̄),
```

that is, `pi(z) = 1` for every homomorphism `pi : T̄ -> U(prod M_n / sum M_n)`.
The proof must not use Property `(T)`, a Kazhdan subgroup, a Kazhdan
projection or Kazhdan transport.

## Equivalent forms and consequences

All of these are proved in `lifted-thompson-t-mf-radical-dichotomy`.

- **Equivalent forms.**  "`T̄` is not MF", "`Rad_MF(T̄) != 1`" and
  "`Rad_MF(T̄) = T̄`".
- **Torsion-free seed.**  `T̄` is finitely presented and torsion-free, so this
  claim gives `property-t-free-torsion-free-fp-non-mf-seed` (route
  `property-t-free-seed-via-lifted-thompson-t`).
- **Thompson's `T` and `V` are not MF.**  This claim implies `Rad_MF(T) = T` and
  `Rad_MF(V) = V`.  The latter is the single hole of the wave-15 Leavitt
  route, which puts `V` inside the binary-Leavitt Steinberg group and pushes
  its radical forward.  It was posted on the live bus as
  thompson-v-is-not-mf and as thompson-v-has-full-mf-radical.
- **Both deep inputs at once.**  So one statement feeds both deep inputs of
  `property-t-free-manuscript-results`: the binary-Leavitt collapse and the
  torsion-free seed.
- **`2V` is not MF.**  By `lifted-thompson-t-embeds-in-cantor-integer-maps-by-v`,
  `T̄ <= C(C,Z) ⋊ V <= 2V`, and a subgroup of an MF group is MF.

## How it fails

This claim is false as soon as any one of the following holds:

- `T` is MF;
- `C_T(r_k)` is MF for one `k >= 0`, where `r_k` is the rotation by `2^(-k)`
  (item 3 of the dichotomy);
- `C(C,Z) ⋊ V` or `2V` is MF.

So it is at least as strong as "`T` is not MF", which is itself stronger
than "`V` is not MF".  It is a hole that can fail on its own, and it shares no
node with the Higman cone, the abelianized-cover hole or the
virtual-torsion corner.

## What a proof must supply

- `T̄` is perfect and has no nontrivial finite-dimensional unitary
  representation.  A finite-dimensional image would be a finitely generated
  linear group, hence residually finite, and `T̄` has no proper finite-index
  subgroup (`lifted-thompson-t-perfect-centre-cubically-elliptic`).  So
  `Rad_fd(T̄) = T̄` holds for free, and all the content is in the transport
  from exact to approximate representations.
- By `compression-defect-dies-in-mf-under-mark-stability`, fd point-norm
  stability of `T̄` at one element of a nontrivial compression-centralizer
  defect would suffice.  Stability of `T̄` is not known.
- Central fibres do not help directly.  A corona representation makes `pi(z)`
  central in `B = C*(pi(T̄))`.  The fibres `B/(pi(z) - mu)` over the spectrum
  of `pi(z)` are arbitrary C-star quotients, not corona subalgebras, so
  `Rad_MF(T) = T` cannot be applied fibrewise.  Nontrivial `mu`-twisted
  representations of `T` exist on Hilbert space for every `mu` in the
  circle: the Bloch decomposition of the Koopman representation of `T̄` on
  `L^2(R)`.  So no fibrewise argument that holds in `B(H)` can force
  `pi(z) = 1`.

## Attempts

**Chromatic-code route with a non-central mark (2026-09-19,
swarm-0917-w17-w17-ptm-last1).**

- **New route.**  `lifted-thompson-t-not-mf-via-chromatic-code` has one open
  leaf, `lifted-thompson-t-bounded-area-chromatic-code`.  Its other inputs,
  `infinite-chromatic-commutator-code-kills-mf-mark` and the dichotomy, are
  ESTABLISHED.
- **Marking `z` is dead** (`central-marks-escape-chromatic-codes`).
  - Commutator codes: the invariant is the translation number.  `[F,G] = z^m`
    makes `FG = z^m GF` conjugate to `GF`, so `m = 0`.  Proofs die at CCC1.
  - Conjugacy-difference codes: the invariant is the Cayley graph of a
    finite conjugacy class, which gives `chi <= 2|C| + 1`.  Proofs die at
    CDC2, in any group.
  - Lifting codes from `T` preserves exactness but not area.
- **Exact skeleton, literal words dead**
  (`lifted-thompson-t-exact-wandering-commutator-table`).
  - Wandering copies of `F` under `x0` give an exact `K_Z` table with a
    non-central mark.
  - The literal shift words have CCC2 area at least
    `(4|m-n| - 2(|c0| + |h0|)) / P`, by a bridge count in van Kampen diagrams.
  - Bounded area needs non-literal words, presumably using the rotation and
    cone relators of `T̄`.
- **w18 ptm-last1 (cohomology-index): annular localization kills
  clique-rich conjugate templates.**  Two new nodes were established by
  written proof:
  - `bounded-area-commuting-conjugator-localization`, for any torsion-free
    finitely presented group.  If `Area([y,h]) <= A`, then `y = h^n g` with
    `g ∈ C(h)` and `|g| <= A M + 2|h|`.
  - `lifted-thompson-t-conjugate-template-codes-have-bounded-cliques`.

  For the chromatic-code route
  (`infinite-chromatic-commutator-code-kills-mf-mark`) in `T̄`, a conjugate
  template `c_v = u_v c u_v^(-1)`, `h_v = u_v h u_v^(-1)` with bounded-area
  cross commutators forces `C_w ∈ u_v F u_v^(-1)` with `F` finite.  The
  invariants are the translation number and the slope spectrum at fixed
  points.  As a result:
  - the clique number is at most `2|F| + 1`;
  - every neighbourhood is finitely colourable;
  - wandering tables die for every choice of words, not only for the literal
    words `x0^n`.

  Survivors:
  - conjugate templates on clique-poor, shift-graph-like (line-digraph)
    graphs;
  - templates that are not conjugate.

  The status stays **OPEN**.
- **2026-09-19 (swarm-0917-w19-w19-ptm-last1, quantifier-shift): a second route that avoids
  the eigencorner hole, and the rate at which it can fail.**
  - *Established.* `central-power-quotient-gaps-converge-to-the-extension-gap`, for any finitely
    presented `G` and generator `z`. Rounding `U_z` to exact `m`-th roots of unity costs
    `Lπ/m` in relator defect. Hence `δ_∞(c) ≤ δ_m(c) ≤ δ_∞(c + π/m) + Lπ/m`, and
    `z ∈ Rad(G)` if and only if the gaps of the quotients `G/⟨⟨z^m⟩⟩` beat `Lπ/m` at one
    `m ≥ π/c` for each `c`. There are no intermediate rates.
  - *New route.* `lifted-thompson-t-not-mf-via-uniform-rotation-centralizer-gaps`, with the one
    open prerequisite `rotation-centralizer-rotation-gaps-are-uniform` (UG). UG is about the
    rotation centralizers `C_T(r_k)` only. It is equivalent to this claim, so the route is a
    lossless reformulation. It bypasses `lifted-thompson-t-centre-has-commutant-eigencorners`
    and its arc-spectrum failure, because no spectral projection of `ρ(z)` is ever taken.
  - *What the equivalence rules out.* Fullness of `T` gives `δ_{2^k}(c) > 0` at each level
    (item 4 of `central-eigencorners-die-over-full-radical-quotients`). That is not enough:
    this claim needs `2^k δ_{2^k}(c) → ∞`.
  - *Where the level-by-level method dies (heuristic).* Deriving level-`k` gaps from a gap of
    `T` by cutting `U_z` into its `2^k` eigenclusters loses a factor of order `2^k`, through
    Fejér polynomials. The resulting bound `≳ κ/(C L 2^k)` sits at the same scale as the
    threshold. Details are under `## Attempts` of `rotation-centralizer-rotation-gaps-are-uniform`.
    Self-similarity through `λ`, and determinant phases, did not help.
  - *Status.* This claim stays OPEN.
- **2026-09-19, swarm-0917-w19-w19-ptm-follow (symbolic-dynamics):
  element-level envelope of conjugate-template codes.**  Established
  `lifted-thompson-t-template-envelope-contains-shift-graphs`.
  - The element-level envelope of conjugate-template codes (the output
    (N) of annular localization) is a union of line digraphs `L(Z_i)`.
    Each `Z_i` is a conjugation orbital digraph of a commuting pair.
    Templates with commensurated centralizer intersections all die.
  - An explicit template in `F ⊂ T̄` lives on the triple shift graph
    `Sh_3(N)` (`chi = infinity`, triangle-free).  It uses affinely
    transported copies of `x_0` on disjoint dyadic intervals, and it has:
    - exact commutation on every edge;
    - CCC1 with area 0;
    - (N) with one-point `F`, `F_1`.
  - So no element-level invariant can kill conjugate templates.
  - The approach dies (or succeeds) only at relator area: the growth of
    `Area([kck^(-1),h])` for the free words `k = u_a^(-1)u_b`.  This is an
    open Dehn-function question.  A bounded answer would kill `x` in every
    MF model of `T̄` and make `T̄` non-hyperlinear.  The expected answer
    is unbounded, by a thin-diagram bridge count.
  - Target stays OPEN.
- **2026-09-20 (swarm-0917-w20-w20-ptm-last1, stability-approximation):
  the chromatic-code lane has a hidden prerequisite, "`T` is not sofic".
  ESTABLISHED as `lifted-thompson-t-chromatic-codes-force-t-nonhyperlinear`.**
  - *Descent.*  A bounded-area commutator code on `T̄` is, with the same
    constants, a code on `T` and on every `C_T(r_k)`, because adding
    relators only shrinks area.  Its mark is a commutator.  By translation
    numbers no nontrivial commutator lies in `⟨z⟩`, so the pushed mark is
    nontrivial.
  - *Criterion.*  Pigeonhole over a finite normalized Hilbert--Schmidt net
    of `U(k)` shows that a finitely presented group with such a code is not
    hyperlinear.
  - *Consequence.*  Any code-based proof of this claim proves that `T`,
    `V` and `2V` are not sofic.  It also makes `T` an explicit nonhyperlinear
    group.
  - *Class kill.*  Conversely, a sofic or hyperlinear `T` kills every
    commutator code, for every mark, on `T̄`, `T` and each `C_T(r_k)`.
    Among them are the wave-19 triple-shift template and all
    conjugate-template survivors.  The point where it dies is (CCC1)/(CCC2)
    evaluated in a Hilbert--Schmidt approximation of `T`.
  - *What remains.*  The target itself stays **OPEN**.  The lanes that do not
    pay this cost are operator-norm-only ones:
    - `lifted-thompson-t-not-mf-via-central-eigencorners`;
    - the uniform rotation-centralizer gap reformulation of wave 19.
- **2026-09-20 (swarm-0917-w20-w20-ptm-follow, host-geometry): the wave-19 Dehn question
  reduced to one function on one group.**  ESTABLISHED as
  `lifted-thompson-t-shift-template-area-is-a-stabilizer-function`.
  - *Exact identity.*  On each Sh_3 arc `a -> b`,
    `Area([C_b,H_a]) = Area([δ c δ^(-1), kappa])`, where `kappa = σ^(-1) h σ` is a fixed word
    for `c_K`, and `δ = σ^(-1) u_a^(-1) u_b` is a word for some `d ∈ D = C(c) ∩ C(c_K)`.
    Hence `Area >= f(d)`, where `f(d)` is the least such area over all words for `d`.
  - *Invariance.*  `f` is invariant under `<c, c_K>`.
  - *Forced infinitude.*  The out-arcs of one vertex already give infinitely many classes of
    `d` in `D/<c,c_K>`, separated by the interval `d(sI) ⊂ [0, 5/16)`.
  - *Kill criterion.*  If `f` is proper (interval-proper suffices), the template dies for all
    words and all choices of free parts.  Whether it is proper is OPEN.
  - *Why the obvious tools fail.*
    - `f` is strictly finer than the localization data: `f(c_K^q) = O(1)`, while the
      commutation area with `c` is unbounded on the `c_K^q`.
    - Length-only bridge counts cannot prove properness.
  - The target stays OPEN.
- **Linear area certificates on conjugate templates (sw-0917-w22,
  2026-09-20).**  This is dead as a class, by
  `thompson-template-area-sees-only-faithful-coefficients`.
  - The edge word `[k c k^(-1), h]` of any conjugate template satisfying
    (N) differs in area by a constant from `[lambda, h]`.  Here `lambda` is
    the null-homotopic conjugacy loop.
  - Its relation-module class is a constant plus `(1-h) cl(lambda)`.
  - Every linear lower bound whose coefficient module is not faithful
    modulo `<z>` is therefore constant on the `Sh_3(N)` template, whatever
    words are chosen.  Such bounds include central extensions (Euler, GV,
    `H_2` torus classes), cocycles from abelian or residually finite
    quotients, and all finite-rank twisted Schreier norms.
  - What remains is (D1), homological area or a permutation module
    `ell^1(T-bar/D)`, or (D2), a genuinely nonabelian obstruction in the
    kernel of `P_omega -> T-bar^omega`.
- **2026-09-20 (swarm-0917-w22-w22-ptm-pull, transplanter /
  entropy-measure): tracial methods reach a sharp dichotomy and then die at
  a named norm-only conjunct.**

  *Transplant tried.*  Push entropy, measure and character arguments
  (normalized traces, ultralimit states, HS defects) through the centre of
  `T̄`.  The first form was "`Res_hyp(T̄) = T̄` iff `T` is not hyperlinear".
  It is not new: it follows at once from the normal-subgroup structure of
  `T̄` and Thom's central-quotient descent (Remark 3.4 in
  `thom-central-corner-criterion`).  It is not recorded as a node.

  *What survived (new, ESTABLISHED).*  `lifted-thompson-t-shadow-residual-dichotomy`:
  - `S(T̄) = R_(infinity->2)(T̄)` is `1` or `T̄`, by the dilation argument of
    the MF dichotomy run on the shadow residual.
  - `T` MF implies `T̄` hyperlinear, hence every Euler-twisted
    `L_(s·eu)(T)` is Connes-embeddable.  One gapped commutant corner of
    `rho(z)` already gives the same conclusion.
  - On the branch `S(T̄) = T̄`, three things hold for every corona map:
    it is a full-trace padding; every commutant corner is HS-invisible in
    its renormalized ultralimit traces; and `sp(rho(z) P)` is connected and
    contains `1` for every nonzero commutant corner `P`, and likewise for
    every `t_k` via `rho ∘ lambda^k`.

  *New exact decomposition.*  `lifted-thompson-t-not-mf-via-gapped-corners`:

  ```text
  this claim  <=>  lifted-thompson-t-shadow-residual-is-full (A, tracial)
                   AND lifted-thompson-t-centre-has-gapped-commutant-corners (EC′, norm only)
  ```

  (EC′) is implied by the eigencorner conjunct (EC) of
  `lifted-thompson-t-not-mf-via-central-eigencorners`, so it is weaker.
  (A) is stronger than `thompson-t-has-full-mf-radical`.

  *Death step (the obstruction for the whole family).*  Every tracial
  invariant (entropy, trace, spectral measure of `rho(z)` for an ultralimit
  trace, character) sees only `S(T̄)`.  So a tracial argument proves at most
  (A).  Under (A), a counterexample `rho` has these properties:
  - it is HS-invisible in every commutant corner;
  - the spectrum of `rho(z)` in every corner is a connected arc through `1`;
  - no approximate corner has error below `|lambda - 1|`.

  This is exactly the configuration of
  `o2-suspension-central-unitary-evades-commutant-corners`.  No ultralimit
  trace of any corner distinguishes `rho` from the trivial representation.
  So the family dies at conjunct (EC′), which is invisible to every
  invariant that the family computes.  It also shows that the w16 cut
  inside `C^*(rho(z))` (on
  `lifted-thompson-t-centre-has-commutant-eigencorners`) never starts under
  (A): the whole of `sp(rho(z))` is then one arc through `1`.

  *Calibrations.*
  - **Modular subgroup.**  The preimage of `PSL(2,Z) <= T` in `T̄` is
    `B_3 = <a, b | a^2 = b^3>`.  Here `a` and `b` lift the generators of
    orders 2 and 3, and `a^2 = b^3 = z = Delta^2`.  `B_3` has the character `sigma_i -> e^(i theta)`,
    which sends `z` to `e^(6 i theta) != 1`.  So no argument that restricts
    to the modular subgroup can succeed; it must use the relators that make
    `T̄` perfect.
- **2026-09-20 (swarm-0917-w23-w23-ptl-pull, transplanter via symbolic-dynamics):
  twist-and-cut; the residual is full-circle rigidity; the target stays OPEN.**
  - *Established* `lifted-thompson-t-corona-centre-spectrum-is-full-circle`, an
    implication.  Assume the T gap `G(eps_0)`, which is equivalent to
    `thompson-t-has-full-mf-radical`.  Put `alpha_0 = min(pi, 24 arcsin(eps_0/2))`.
    - *Central twist.*  If `sp(rho(z))` lies in an arc of half-width `alpha < alpha_0`, then
      untwisting by `u = rho(z)^(1/12)` gives an exact `Z/4 * Z/3` pair with
      `r_1 = r_2 = 1` and pentagon defect `||u - 1|| <= 2 sin(alpha/24)`.  So `rho` is
      trivial.
    - *Short pieces.*  Tensoring a corner with its conjugate kills every clopen piece of
      `sp(rho(z))` shorter than `alpha_0`.
    - *Dilation.*  The dilation `lambda` (`t_(k+1)^2 = t_k`) spreads the remaining arcs.
    - *Result.*  Every nontrivial corona representation has `sp(rho(t_k)) = S^1` at
      every level `k`, in every commutant corner it moves, and levelwise along every
      subsequence on which it stays nontrivial.
  - *Reduction.*  The target is equivalent to `thompson-t-has-full-mf-radical` plus
    (FC): no nontrivial corona representation has full-circle centre in all of these
    senses.  This sharpens the "Where it already holds" paragraph of
    `lifted-thompson-t-centre-has-commutant-eigencorners`, where "perfect away from 1"
    becomes "the whole circle".
  - *Class killed: central functional-calculus twists and cuts.*  These are twists or
    cuts of `rho` made with the functional calculus of `rho(z)`, of `rho(t_k)`, or of
    tensor powers `rho^(⊗p) ⊗ conj(rho)^(⊗q)`.
    - *Invariant.*  The degree vector `(1,...,1,-1,...,-1)` of the centre on the joint
      spectrum `(S^1)^(p+q)` is not divisible by 12.
    - *Failure step.*  The twelfth root `u` with `u^12 = rho(z)` does not exist.  The
      residual exponent in `(B'A')^5 = u^(36-35)` is the Euler number 1.
    - *Where the class dies.*  Exactly on (FC).  A witness for (EC) must come from
      commutant projections outside `C^*(rho(t_k))` and its tensor powers.
  - *Next falsifiable step.*  Decide whether an (FC) representation can exist.  A
    candidate for building one is a sequence of exact pairs in which the spectrum of
    `(BA)^5` equidistributes on the circle while the defect of `r_1` and `r_2` tends to 0.
    Such a sequence would refute the T gap and settle `thompson-t-has-full-mf-radical`
    negatively.  Conversely, no (FC) representation exists at all if the T gap holds with
    every corner forced to be a scalar.
- **2026-09-20 (swarm-0917-w23-w23-ptm-pull, transplanter / probability-random): class-kill of
  bounded-Lie-closure amplification.  Established
  `lifted-thompson-t-twisted-witnesses-need-unbounded-lie-closure`.  The target stays OPEN.**
  - *Result.*  Let `σ` be an exact representation of `K(3,4) = <x, y | x^4 = y^3>`, and let
    `N` be the dimension of the semisimple part of the Lie algebra of the closure of `σ(K)`.
    Suppose the `T̄` defect satisfies `D < min(1/2, δ_N/2)`, where `δ_N` is the untwisted gap
    of `T` over `Z4 * Z3` in dimension `<= N`.  Then `σ` is abelian, `x ↦ u^3`, `y ↦ u^4`,
    and the twist satisfies `||σ(x^4) - 1|| <= 12 D`.  The constant `12` is sharp.
  - *Device.*  `Ad ∘ σ` on the complexified semisimple part kills the centre.  So it is a
    `Z4 * Z3`-representation of dimension `N` with `T` defect `<= 2D`.  Below `δ_N` it is
    trivial, which makes the closure virtually a torus, and the virtually-solvable-image lemma
    finishes.
  - *Consequence.*  Every asymptotic representation of `T̄` with defect `→ 0` and scalar twist
    bounded away from `1` has semisimple Lie closure of unbounded dimension.  So no witness
    against this claim comes from `Sym^m` or tensor powers of a fixed compact pair, from any
    finite or virtually solvable quotient of `K(3,4)` or of the Brieskorn lattice, or from
    random models in a fixed compact group.
  - *Where it stops.*
    - The bound is only as strong as `δ_N`.  A disproof must make `T` itself nearly MF at the
      growing dimension `N` while keeping the twist.
    - Non-scalar twists need the eigencorner step (EC) first, which is still open.
  - *Evidence.*  `experiments/lifted-t-lie-closure-gap-2026-09-17/`.
    - `Sym^1` of an `SU(2)` pair gives a twisted, nonabelian `D = 2 sin(π/24)`.
    - Its `Sym^2` is an exact `SO(3)` representation of `T`'s free product with
      `D_T = 2 sin(π/12)`.  So the factor `2` of the adjoint transfer is nearly attained.
