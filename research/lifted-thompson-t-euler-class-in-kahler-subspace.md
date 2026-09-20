---
rg: 2
id: lifted-thompson-t-euler-class-in-kahler-subspace
kind: claim
title: "(K): the real Euler class e_R of Thompson's T is a cup product [b_1 ∪ b_2] of two 1-cocycles into one orthogonal representation of T (equivalently, e_R is the area class Im<b(g), pi(g) b(h)> of one unitary cocycle)"
distinct_from:
  lifted-thompson-t-root-twist-cost-iff-euler-cup-product: that proves (K) implies T-bar Haagerup and characterizes (K) by the square-root twist rate; this is (K) itself
  thompson-t-euler-class-splits-over-almost-invariant-space: that asks for a measurable splitting of the Euler cocycle over a nonsingular T-space (the MT route); this asks for a Hilbert-space cup-product representative, with no splitting
  cup-products-of-integrably-paired-potential-cocycles-are-exact: that kills the witness class of cocycles with integrably paired potentials; this is the open statement those witnesses would have proved
artifacts: []
---

**Statement.** There are an orthogonal representation `π` of Thompson's group `T` on a real
Hilbert space and 1-cocycles `b_1, b_2` into `π` such that
`e_R = [(g,h) ↦ ⟨b_1(g), π(g) b_2(h)⟩]` in `H²(T; R)`.

**Status.** OPEN.

## Role

- Last missing prerequisite of `lifted-thompson-t-a-t-menable-via-kahler-euler-class`, a route to
  `lifted-thompson-t-is-a-t-menable`, which is necessary for `brin-thompson-groups-nv-are-a-t-menable`.
- It can fail on its own. By part (3) of `lifted-thompson-t-root-twist-cost-iff-euler-cup-product`,
  its failure forces `c(θ)/√‖θ‖ → ∞`. It mentions only `T`.

## Forced shape of a witness

- Not one real cocycle in a complexified representation (area 0,
  `lifted-thompson-t-root-twist-cost-iff-euler-cup-product`).
- Not a pair with an integrably paired potential in a common Koopman model
  (`cup-products-of-integrably-paired-potential-cocycles-are-exact`). This excludes every measured
  wall structure and every cube complex action of `T`, so all of the Haagerup machinery of `T`.
- The model to imitate: `e_R` is the symplectic area class of the displacement cocycle
  `u_g = g̃ − id` in 1-periodic functions with `ω(φ, ψ) = ∫_0^1 φ dψ`
  (Step 3 of `integrably-paired-cup-products-exact-proof`). A witness is
  a unitarization of this symplectic picture: a `T`-invariant Hilbert structure compatible with the
  area on a module carrying a cocycle cohomologous to `u`.

## Attempts

- **2026-09-18 (swarm-0917-w13-w13-nv-follow, cohomology-index): the integrable-potential class dies;
  the symplectic model of `e_R`.**
  - *Established.* `cup-products-of-integrably-paired-potential-cocycles-are-exact`. The invariant is
    the renormalized pairing `N(g) = ∫ f̄ b_2(g) dμ`. Every member dies at the expansion
    `⟨π(g)f − f, π(g)b_2(h)⟩ = N(g) + N(h) − N(gh)`, which needs only invariance of the absolutely
    convergent pairing.
  - *Why the displacement model does not unitarize directly.*
    - `T` acts on PL periodic functions by composition. Restricted to dyadic points, this is a
      permutation of `D`. `T` is transitive on ordered pairs of distinct dyadic points, so every
      `T`-invariant kernel on `D × D` has the form `aδ + b`. Such a kernel gives no finite
      invariant form on nonconstant functions.
    - Invariant data at a dyadic point (the one-sided slopes) transform by powers of 2. That is a
      monomial representation with non-unimodular scalars, not a unitary one.
    - So the natural module `(W, ω)` of the Euler class carries no evident `T`-invariant
      positive form dominating `ω`. This is recorded as an obstacle, not as a theorem: `W` is only
      one module, and (K) allows any.
  - *Positive lead, not pursued (posted as spark).* By Ghys–Sergiescu, `T` is conjugate into
    `Diff^∞(S^1)` (recalled, not verified). Smooth diffeomorphisms lie in the restricted symplectic
    group of `H^{1/2}(S^1)/R`, while PL ones do not, because `log g'` has jumps. In the smooth model
    the displacement cocycle quantizes as `W(√t u_g) M(g)` with the metaplectic `M` on Fock space.
    Its multiplier is `e^{it·area}` times the fixed Bott–Virasoro multiplier. Tensoring with
    `M̄` removes the latter and gives genuine representations of `T̄` with `z ↦ e^{±it}`. Twist cost
    `→ 0` would then need `M ⊗ M̄` (the conjugation action on Hilbert–Schmidt operators on Fock
    space) to have almost invariant vectors for `T`. That is the falsifiable next question on this
    lead.
- **2026-09-19 (swarm-0917-w15-w15-nv-last1, operator-algebras): the smooth-model witness classes
  die; the noncommutative pairing.**
  - *Established.* `trace-class-conjugation-cocycles-have-exact-cup-products`.
    - The invariant is the relative trace `N(g) = Re tr(F^* b_2(g))`.
    - Every conjugation cocycle `U F U^* − F` with `F ∈ S_p` (`2 ≤ p ≤ ∞`, `S_∞ = B`) has exact
      cup product with every `S_{p'}`-valued partner. So all pairs from the trace-class commutant
      algebra `A_1(U)`, plus `S_2`, are killed.
    - For any action of `T` by `C³` circle diffeomorphisms, the Hilbert-transform (Connes)
      Fredholm-module cocycle is trace-class valued. The commutator kernel is `C¹` on the torus.
    - The Navas–Liouville cocycle has `L¹(μ)` values.
    - So both canonical sources of unitary cocycles for smooth circle groups are excluded as
      (K)-witnesses. This includes the two natural unitary objects of the Ghys–Sergiescu model.
  - *Where a witness could still live, among conjugation models.* It needs a potential whose
    relative trace against the partner diverges: a Hilbert–Schmidt but not trace-class commutator
    structure that no `(S_p, S_{p'})` pairing absorbs.
  - *Not pursued.* The `M ⊗ M̄` question from the w13 spark is a separate route through the
    twist cost, not a (K)-witness. The observation below is made informally, with no proof
    written:
    - the Weyl symbol identifies `M ⊗ M̄` with a Koopman representation of a nonsingular Gaussian
      action of smooth `T`;
    - so its Gaussian vectors are almost invariant iff `T` has almost fixed points in the
      Hilbert–Schmidt Siegel disk.
- **2026-09-19 (swarm-0917-w15-w15-nv-follow, reframing): the metaplectic lead made precise;
  (K) stays OPEN.**
  - *Established.* `lifted-thompson-t-farey-fock-twist-bound`. No Ghys–Sergiescu smoothing is
    needed. In the Farey model `T ≅ PPSL_2(Z)`, breakpoints are cusps and the pieces differ by
    parabolics, so every element is `C^1` with Lipschitz `log g'`. That puts it in the
    Weil–Petersson class, so `T` acts through `Sp_res(H^{1/2}/R)` and gives the Farey–Fock
    representation `M`.
  - The Weyl-twisted representations `W(√t b)M ⊗ M̄` of `T̄` give
    `c(t/4π) ≤ K|t| + B√(2|t|(1+n(ρ))) + δ(ρ)^{1/2}`. Conversely, every vector has defect at least
    `δ_*/2`, where `δ_*` is the Bekka defect of `M|_T`.
  - *Consequences for this node.*
    - The w13 spark is exactly the question "is `M|_T` Bekka-amenable?".
    - If no, the metaplectic lead dies, along with every `V ⊗ M̄` family.
    - If yes, relative (T) of the centre is refuted.
    - If yes with a subexponential particle-number profile, `T̄` is Haagerup without (K).
    - An exactly invariant normal state with finite second moment would give the (K) rate `O(√θ)`.
      No such state is known, so (K) is not decided.
  - *The w13 PL obstacle, explained.* It is a model artefact: dyadic `log g'` jumps, while Farey
    `log g'` only has kinks.
- **2026-09-19 (swarm-0917-w16-w16-nv-pull, cohomology-index): the metaplectic lead is dead in
  the Farey model; (K) stays OPEN.**
  - *Established.* `farey-fock-representation-of-t-is-not-bekka-amenable`: `δ_* > 0`, so (Q1) is NO.
  - *Invariant.* The spectral gap of the lattice `PSL_2(Z)` on the particle sectors
    `Sym^m(D_2) ⊗ conj Sym^n(D_2)` (`m + n ≥ 1`) of `HS(F)`. These are tempered for `PSU(1,1)`,
    because `D_2` is square-integrable (Fell absorption), and Kesten turns this into a gap.
  - *Step where it dies.* An almost invariant density `ρ` has `ρ^{1/2}` close to `P_Ω`. A
    vacuum-fixing element preserves the one-particle norm, so it commutes with `J_0` and maps `z`
    into `H^2`. The argument principle then makes it a single Möbius map, but `T ≠ PSL_2(Z)`.
  - *Consequences for this node.* Every `W(√t b)M ⊗ M̄` and every `V ⊗ M̄` family gives nothing.
    There is no invariant normal state either, so the `O(√θ)` sub-route is also closed.
  - *What survives.* Fock or Gaussian models over a complex structure `J` that no non-amenable
    subgroup of `T` preserves with a tempered one-particle representation. Any other circle model
    in which a non-amenable subgroup of `T` acts through a lattice of `PSU(1,1)` dies the same way.
- **2026-09-20 (swarm-0917-w20-w20-nv-break, cohomology-index): the dilation dichotomy; (K)
  reduces to one cup product off the Godbillon–Vey line. (K) stays OPEN.**
  - *Established.* `thompson-t-cup-classes-split-along-dilation-eigenlines`.
    - The realizable classes `K` form a linear subspace, closed under direct sums and scalings.
    - `K` is invariant under the transfer `J = (p^*)^{-1} i^*` through the half-rotation
      centralizer `C_T(x ↦ x + 1/2)`, whose descent `p` has central kernel `Z/2`. This works
      because cup products average onto `H^A` and descend.
    - `J(e_R) = e_R/2`: translation numbers double under the descent.
    - `J(gv) = 2 gv`: discrete Godbillon–Vey sums halve. Here `gv` is checked nonzero on an
      explicit torus, `⟨gv, σ_t⟩ = 2`, with exact checks in
      `experiments/kahler-dilation-2026-09-17/check_gv_dilation.py`.
  - *Consequences for this node, with [GS] `H²(T; R) = R²`.*
    - `K ∈ {0, R e_R, R gv, H²}`.
    - So (K) ⇔ some cup product is not a multiple of `gv`. Equivalently, some non-exact cup
      product vanishes on the one torus `(g_0, h_0)`.
    - From any `c = λe_R + μ gv ∈ K` with `λ ≠ 0`, the witness is `2c − J(c) = (3/2)λ e_R`.
      So the Godbillon–Vey component of a candidate never has to be cancelled.
  - *Growth test.* `|μ| ≤ 2^{-n-1}(‖b_1(g_n)‖‖b_2(h_n)‖ + ‖b_1(h_n)‖‖b_2(g_n)‖)` on the dyadic
    towers `g_n, h_n`.
    - So every non-exact cup product with `o(2^{n/2})` cocycle growth on the towers gives (K).
    - `gv` can only be carried at the `ℓ²`-additive rate of the breakpoint-jump cocycle.
  - *Next falsifiable steps.*
    - Is `gv ∈ K`? Test the jump cocycle in `ℓ²(Z[1/2]/Z)` against a second local cocycle.
    - Does some Farley cube-complex cocycle have sub-`2^{n/2}` growth on the towers? Such
      cocycles have exact cup products (w13 kill), so the test there is only a consistency
      check.
    - A genuine witness must pair nontrivially with the `1/2`-eigencycle `σ_e` of `J_*`.
