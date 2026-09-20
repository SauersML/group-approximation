---
rg: 2
id: lifted-thompson-t-is-a-t-menable
kind: claim
title: "The lift T-bar of Thompson's T to the real line (the central extension of T by Z with the Euler class) has the Haagerup property"
distinct_from:
  thompson-v-has-haagerup-property: that is Farley's theorem for V, and so for T ≤ V; this asks it for the central extension T-bar of T by Z, which is not a subgroup of V at all (it contains Z[1/2], excluded from V by Higman; see lifted-thompson-t-escapes-haagerup-permanence-closure)
  cantor-integer-maps-by-v-have-haagerup-property: that is Brothier's Problem B for Γ = Z, for the group C(C,Z) ⋊ V; this is its one-dimensional subcase for the subgroup T-bar ≤ C(C,Z) ⋊ T, which it implies but is not known to imply it
  lifted-thompson-t-center-has-relative-t: that is the refuting statement (relative (T) for the centre); this claim implies its negation
artifacts: []
---

**Statement.** Let `T̄` be the group of lifts of Thompson's `T` to `R`, with central translation
`z(x) = x + 1`. Then `T̄` admits a proper conditionally negative definite function.

**Status.** OPEN.

## Role

This is **necessary** for `brin-thompson-groups-nv-are-a-t-menable` and for
`cantor-integer-maps-by-v-have-haagerup-property`, because
`T̄ ≤ C(C,Z) ⋊ T ≤ C(C,Z) ⋊ V ≤ 2V` (`lifted-thompson-t-embeds-in-cantor-integer-maps-by-v`).
It can fail on its own: its failure refutes both.

It is the smallest known subgroup of `2V` in which the central direction
(`cantor-integer-maps-central-direction-has-relative-t`) can be tested. The centre `⟨z⟩` goes to
`Z·1_C`.

## Equivalent form

`T` has the Haagerup property, since `T ≤ V` (`thompson-v-has-haagerup-property`). Pull a
proper cnd function of `T` back to `T̄`. The result is proper modulo `⟨z⟩`, because its sublevel
sets are finite unions of fibres of `T̄ → T`, and those fibres are cosets of `⟨z⟩`. By
`haagerup-splits-as-coset-plus-subgroup-properness` with `H = ⟨z⟩`:

> `T̄` is Haagerup **iff** some cnd function on `T̄` is proper on `⟨z⟩`.

A cnd function that is merely *unbounded* on `⟨z⟩` means exactly that `(T̄, ⟨z⟩)` is not
relatively (T). That is necessary for the claim. Whether it is sufficient for this central `Z` is
not settled here.

## Where this sits in the literature

It is an instance of an open problem. Gomez Aparicio, Julg and Valette, *The Baum–Connes
conjecture: an extended survey*, arXiv:1905.10081, p. 96, verbatim:

> "The behavior of the Haagerup property under central extensions is a widely open question.
> More precisely: if Z is a closed central subgroup in the locally compact group G, is it true that
> G has the Haagerup property if and only if G/Z has it? Both implications are open. See
> Proposition 4.2.14 and Section 7.3.3 in [CCJ+01] for partial results on lifting the Haagerup
> property from G/Z to G, in particular from SU(n,1) to ~SU(n,1)."

Two caveats:
- The contents of CCJJV Proposition 4.2.14 were **not checked verbatim**. If its hypotheses hold for
  `T̄ → T`, this claim closes, and the refutation route through
  `lifted-thompson-t-center-has-relative-t` dies. **Checking it is the cheapest next step.**
- No source stating the Haagerup property of `T̄`, or its failure, was found (searches of
  2026-09-18).

Kida, arXiv:1309.3739, links the pair property to stability: if `(G, C)` does not have (T), then
`G` is stable.

## Attempts

- **2026-09-18 (swarm-0917-w8-w8-nv-last1, host-geometry): first probes.**
  - *Witness form.* Since `z` is central, a witness for non-relative-(T) can be cut down along the
    spectral projections of `π(z)`. Each such projection commutes with `π(T̄)`, and some spectral
    band keeps the relative defect, by averaging `Σ_s ‖π(s)P_j ξ − P_j ξ‖²` over bands. So a
    witness amounts to unitary representations of `T̄` in which `z` acts with spectrum in narrow
    bands near, but away from, `1`. Disintegrated, these are projective representations of `T`
    with multiplier `e(θ·c)`, where `θ → 0` and `c` is a `{0,1}`-valued Euler cocycle, and they
    have almost invariant vectors. This is a sketch; the disintegration step is not written out.
  - *Permutation witnesses on dyadic orbits: die.* Let `O ⊂ R` be a `T̄`-orbit. Then `z` acts
    freely on `O`, so `ℓ²(O)` has no `z`-invariant vector, and almost invariant vectors would make
    it a witness. They do not exist:
    - Let `ξ` be `ε`-invariant under the generating set `X` of (TC1). Then `|ξ|²` is
      `2ε`-invariant in `ℓ^1`.
    - Summing over the `z`-orbits gives a probability `g` on `O/Z`, which is a `T`-orbit in
      `S^1`. It is still `2ε`-invariant under the image of `X`.
    - The Namioka layer-cake argument gives a finite level set `F' ⊂ S^1` with
      `Σ_s |sF' Δ F'| ≤ 2ε|X|·|F'|`.
    - For `ε < 1/(14 L |X|)` this contradicts (TC1) of `thompson-t-orbits-carry-no-invariant-means`. The same argument kills `ℓ²` of any countable
    `T̄`-set whose `Z`-quotient maps finite-to-one and equivariantly to `S^1`.
  - *Virtual splitting is unavailable.* `T` is simple and infinite, so every finite-index
    subgroup of `T̄` maps onto `T`. A virtual splitting would make the rational Euler class of `T`
    zero. It is recalled as nonzero (Ghys–Sergiescu), but that is unverified. So the braid-group
    mechanism does not apply: `B_3` is the lift of `PSL_2(Z) ≤ T`, and the class is torsion there.
  - *Cubical approaches are not excluded by the `2V` kills.* The Callard–Salo distortion and the
    cubical ellipticity of `1_C` concern `2V` and `C(C,Z) ⋊ V`. They do not pass to the subgroup
    `T̄`: a commensurating action of `T̄` need not extend to one of `G`, and `z` is undistorted in
    `T̄`, since `rot(z^N) = N`. One constraint does remain. In any `T̄`-action on a
    finite-dimensional CAT(0) cube complex with `z` hyperbolic, the minset splitting gives a
    homomorphism `T̄ → R` nonzero on `z`. So `z` is not hyperbolic there when `Hom(T̄, R) = 0`,
    which again reduces to the nonvanishing of the rational Euler class.
  - *Next falsifiable steps.*
    - (a) Read CCJJV Proposition 4.2.14 and §7.3.3 verbatim, and test their hypotheses on `T̄`.
    - (b) Try the twisted "complementary series" family: `T̄` acting on `θ`-quasi-periodic
      functions on `R` with density weight `(a^(-1))'^(1/2+s)`, where `z` acts by the scalar
      `e(−θ)`. Ask whether it has almost invariant vectors as `θ → 0`. For `θ = 0` this is the
      twisted Koopman question for `T` on `S^1`.
- **2026-09-18 (swarm-0917-w9-w9-z-break, entropy-measure): the order-convex wall class dies.**
  - *Result (ESTABLISHED, `lifted-thompson-t-convex-line-walls-are-trivial`).* `T` preserves no
    nonzero Radon measure on `(S^1 × S^1) \ Δ`.
    - Proof: for disjoint dyadic arcs `A, B`, two elements of `T` contract `A × B` onto two
      different corners.
    - Consequence: every `T̄`-invariant measured wall structure on `R` with order-convex walls
      has `d(p,q) = μ{p} + μ{q}`. So its cnd function is bounded on all of `T̄`. The same holds
      for walls pulled back along equivariant maps to `R`, and for walls indexed by intervals of
      `R` through a locally finite measure.
  - *Where every member dies.* The step is "the index measure on endpoint pairs is Radon". The
    winding class `⌊y − x⌋` is `T̄`-invariant, and in each class the measure descends to a
    `T`-invariant Radon measure on `U` or on `S^1`, which is zero.
    - This kills the lifted-Liouville template taken from Fuchsian lattices, which uses
      `dx dy / sin²(π(x−y))`.
    - A cnd function proper on `⟨z⟩` needs walls that are not convex on the lifted line, but
      must still detect the winding.
  - *Remark, not verified.* The divisibility `z = r_k^(2^k)`, where `r_k(x) = x + 2^(-k)` lies in
    `T̄`, should make `z` elliptic in every action of `T̄` on a finite-dimensional CAT(0) cube
    complex. The input is Haglund's combinatorial semisimplicity (arXiv:0705.3386, not read
    verbatim): after cubical subdivision, a hyperbolic automorphism has an integer translation
    length `≥ 1`, so `ℓ(z) = 2^k ℓ(r_k)` is impossible. If this holds, the Euler-class caveat in
    the previous attempt's cubical constraint is unnecessary.
  - Unchanged: this does not decide the claim. Steps (a) and (b) above remain the next steps.
- **2026-09-18 (swarm-0917-w9-w9-nv-last1, reframing): two class-kills and the forced shape.**
  Status stays OPEN.
  - *Cubical: dead (established).* `lifted-thompson-t-perfect-centre-cubically-elliptic`.
    - `T̄` is perfect. For each `n` some `ĝ ∈ T̄` has `ĝ^n = z` (lift an order-`n` element of `T`
      permuting `n` dyadic arcs), so `[z] = nm[z]` in the cyclic group `T̄^ab`.
    - It has no proper finite-index subgroup. So the commensurating lemma makes `z` elliptic in
      every commensurating action of every overgroup.
    - This answers the w8 "cubical not excluded" negatively. It also removes the Euler-class
      caveat: `Hom(T̄, R) = 0` unconditionally.
    - Maruyama, arXiv:2002.12743 §2.1, states `~T = [~T, ~T]` verbatim.
  - *Extractable: dead (established).* `lifted-thompson-t-extractable-cocycles-bounded-on-centre`.
    - Named invariant: paradoxicality of `T ↷ S^1`. Three elements `h_1, h_2, h_3` give
      `c(ρ) ≥ 1/100` for every representation with a circle measure extraction.
    - Step where each member dies: the commuting identity
      `(ρ(h) − 1) b(z^M) = (ρ(z^M) − 1) b(h)`, which gives `ψ(z^M) ≤ 400 Σ ψ(ĥ_i)`.
    - Killed:
      - covariant PVMs on `S^1`, that is all circle-groupoid representations. So the splitting
        `T̄ ⋉ S^1 ≅ (T ⋉ S^1) × Z` transfers nothing.
      - Koopman on any space over `S^1`: `R`, pairs, orbits (subsuming the TC1 kill), and
        measured walls labelled in `S^1`.
      - The `s = 0` member of next step (b), for every `θ`, uniformly.
      - Weak limits of all of these.
    - The `s ≠ 0` members of (b) have no unitary structure specified, so they are not covered.
  - *Centre-fixed part carries nothing.* Since `T̄` is perfect, `b(z^M)` has zero component in
    `H^z`.
  - *Forced shape of any witness.* The cocycle's part `ρ_1` on `(H^z)^⊥`:
    - has no `z`-invariant vectors;
    - has `{ĥ_i}`-almost invariant vectors;
    - is weakly contained in no circle-extractable representation.
  - *(a) CCJJV 4.2.14.*
    - Still not found verbatim.
    - The gHAP definition (CCJJV Def 4.2.1) was reached through Kida, arXiv:1309.3739.
    - Kida's class `C` does not contain `T`, because `T` is simple and not treeable. So Kida's
      route does not decide `T̄`.
  - *Residual quotients (new decomposition).*
    - Rescaling `R/2^kZ` to `S^1` gives an embedding `ι_k : T̄/⟨z^{2^k}⟩ → T` onto the
      centralizer of the rotation `r_k` by `2^{-k}`, with `ι_k(z) = r_k`.
    - So for cnd `ψ_k` on `T` and weights `a_k ≥ 0`, `ψ = Σ_k a_k ψ_k∘ι_k` is cnd on `T̄`
      whenever it converges on a finite generating set `S`. Then `ψ(z^{2^j}) = Σ_{k>j} a_k ψ_k(r_{k−j})`.
    - *Sufficient condition for negating `lifted-thompson-t-center-has-relative-t` (not proved).*
      It suffices to have `sup_k Σ_{s∈S} ψ_k(ι_k s) < ∞` and `ψ_k(r_m) ≥ f(m)`, with `f` growing
      fast enough that `Σ_{k>j} a_k f(k−j)` is unbounded for some summable `(a_k)`.
    - *Dead end: Farley's `ψ_k`.* The periodic images `ι_k(s)` have about `2^k` carets, so the
      convergence forces `a_k = o(2^{-k})`. The resulting `ψ` stays bounded on `⟨z⟩`. This is
      sketched only, not written out.
- **2026-09-18 (swarm-0917-w9-w9-nv-follow, probability-random): measurable Euler splitting.**
  Status stays OPEN.
  - *Sufficient criterion (established).*
    `central-extension-haagerup-from-measurable-euler-splitting`.
    - Hypotheses: `T` is Haagerup, and there is a nonsingular `T`-space `X` whose Koopman
      representation has almost invariant vectors.
    - If some measurable cocycle `β : T̄ × X → R` has `β(z, ·) = 1`, then `T̄` is Haagerup.
    - Mechanism: in the skew product `X × R`, `z` is unit translation, and flat bump vectors
      have coefficients that decay along `z`-cosets.
    - No integrability of `β` is needed.
    - New route: `lifted-thompson-t-a-t-menable-via-measurable-euler-splitting`.
  - *Class-kill (established).* `perfect-extension-splittings-are-not-uniformly-integrable`.
    - Named invariant: `Hom(T̄, R) = 0`.
    - Death step: averaging `β` against the almost invariant densities gives an asymptotically
      additive function, whose ultralimit is a homomorphism with `u(z) = 1`.
    - Killed:
      - every uniformly integrable splitting, including bounded ones and `L¹` ones over pmp
        spaces;
      - through the bounded integer-part splitting over `S^1`, every `T`-space mapping
        equivariantly to `S^1`. This recovers the Koopman half of the circle kill from
        perfectness alone.
  - *New holes (OPEN), each able to fail on its own.*
    - `thompson-t-euler-class-splits-over-almost-invariant-space` (MT).
    - Its discrete case `thompson-t-co-amenable-subgroup-kills-real-euler-class`: a co-amenable
      `H ≤ T` with `e_R|_H = 0`. Such an `H` has no finite orbit on `S^1` and is nonamenable.
    - Concrete test: is `PSL_2(Z)` (preimage `B_3`) co-amenable in `T`? A yes proves this claim.
- 2026-09-18 (swarm-0917-w10-w10-nv-pull, cohomology-index): a `C^0`-continuity kill inside (MT),
  with a Fuchsian calibration. Status stays OPEN.
  - *Class-kill (established).* `thompson-t-c0-continuous-affine-actions-are-trivial`.
    - Named invariant: unitary triviality of `Homeo+(S^1)` and `Homeo~(S^1)`. Point stabilizers
      are `≅ H+[0,1]` (Megrelishvili 2001), and point-fixing elements generate. `T` and `T̄` are
      `C^0`-dense in these groups.
    - Death step: `C^0`-continuity extends the representation to the closure, where it is
      trivial. So `κ = 1`, `T` acts trivially a.e., and `β(·, x)` is a homomorphism `T̄ → R`
      with `z ↦ 1`, contradicting perfectness.
    - Killed:
      - every C^0-continuous unitary representation, affine action or cnd function of `T` or
        `T̄`;
      - every (MT)-witness with `C^0`-continuous Koopman representation, including every
        `T`-invariant probability on a Polish space with a continuous `Homeo+(S^1)`-action;
      - in particular the transplant `Homeo+(S^1)/PSL2(Z)` of the Fuchsian witness, which
        carries no `T`-invariant probability at all. This holds with `β` arbitrary measurable
        and `X` not mapping to `S^1`.
  - *Calibration.* `Δ̃(2,3,7)` is perfect with a bounded Euler class, like `T̄`, yet it has a pmp
    witness `PSL2(R)/Λ_0` with `Λ_0` a free lattice. So what separates `T̄` from the Fuchsian case
    is the unitary triviality of its `C^0` closure, not perfectness.
  - *What survives.*
    - (MT)-witnesses whose Koopman representation is `C^0`-discontinuous (dyadic, PL or
      breakpoint data, such as `T/H` or Farley-type cubical data).
    - Merely quasi-invariant measures on circle-functorial spaces.
    - The co-amenability test for `PSL2(Z)` is untouched, since invariant means are not measures.
- 2026-09-18 (swarm-0917-w11-w11-nv-follow, operator-algebras): exact spectral reduction to the twist cost.
  Status stays OPEN.
  - *Characterization (established).* `lifted-thompson-t-haagerup-iff-twist-cost-spectral-measure`.
    - This claim holds iff some σ-finite measure `ν` on `(R/Z) ∖ {0}` has `∫ c² dν < ∞` and
      `Φ_ν(n) = ∫ |e(nθ) − 1|² dν → ∞`. Here `c` is the twist cost of
      `lifted-thompson-t-relative-t-forces-dyadic-twist-gap`.
    - Necessity: take Schoenberg states `e^{−4^{-j}ψ}` and bound `∫ c² dμ_j` by a spectral Fatou
      inequality.
    - Sufficiency: lift `ν` by Hahn–Banach to the compact space of `z`-twisted states. No
      measurable selection is needed.
  - *Explicit test (established).*
    - `Σ_k c(2^{-k})² < ∞` implies this claim.
    - Form internal to `T`: eigenvectors `ρ_k(r_k)ξ_k = e(2^{-k})ξ_k` whose `ι_k(S)`-costs are
      square-summable.
    - Relative (T) of the centre forces `liminf c(2^{-k}) > 0`, so the problem is now sandwiched
      between two growth regimes of the single sequence `c(2^{-k})`.
  - *What is left (OPEN).*
    - Estimate `c(2^{-k})`. The only known bound is `c(2^{-k}) ≥ 4·2^{-k}/L`.
    - Any family of `T`-representations with `e(2^{-k})`-eigenvectors of `r_k` whose cost is
      `O(k^{-1/2-ε})` proves this claim.
    - The intermediate regime, where `c(2^{-k}) → 0` but not square-summably, is decided only by
      non-dyadic or non-geometric `ν`.
- **2026-09-18 (swarm-0917-w12-w12-nv-follow, cohomology-index): the square-root twist regime is
  the Euler cup product.** Status stays OPEN.
  - *Established.* `lifted-thompson-t-root-twist-cost-iff-euler-cup-product`, via its `-proof`
    route.
    - (1) *Floor.* A second-order expansion of a zero-exponent word for `z` gives
      `c(θ) ≥ 2√(2‖θ‖)/m`.
    - (2) *Kähler lift.* Suppose `e_R ∈ V_T`, where `V_T` is the subspace of classes
      `Im⟨b(g), π(g)b(h)⟩`, equivalently of cup products `b_1 ∪ b_2` for orthogonal
      representations of `T`. Then the phased Weyl operators
      `ρ_t(z^nσ(g)) = e^{−itn} e^{itβ(g)} W(√t b(g), π(g))` on Fock space are genuine
      representations of `T̄`. They give `c(θ) = O(√‖θ‖)` and a proper cnd function
      `ψ_0∘p + Σ_k 2^{k/2}(1 − Re⟨Ω, ρ_{π2^{−k}}Ω⟩)`. So this claim follows.
    - (3) *Converse.* If `c(θ_n) = O(√‖θ_n‖)` along one sequence `θ_n → 0`, an ultralimit of the
      rescaled cocycles `(π_nξ_n − ξ_n)/√|θ_n|` produces a cocycle of `T` whose area class is a
      nonzero multiple of `e_R`. So `e_R ∈ V_T`.
  - *New decomposition.* This claim follows from **(K)**: `e_R ∈ V_T`, a statement about
    Thompson's `T` alone. (K) is also necessary for the optimal twist rate. (K) can fail on its
    own, and does fail if the centre has relative (T).
  - *Guidance.*
    - Real cocycles give `ω = 0`, so Farley's cocycle by itself contributes nothing. A witness
      needs two cocycles into one orthogonal representation whose antisymmetric cup product is the
      Euler cocycle up to a coboundary.
    - The surface-group analogue holds with trivial coefficients.
  - *Side observations, sketched only and not written as nodes.*
    - Twisting Jones-type representations of `T` by a character of the centre reduces to
      representations of `C(C, Z) ⋊ T`.
    - Pythagorean-type representations restrict to extractable ones on the centre, so they do not
      twist.
    - The barycentric extension of the band-cut witness is subsumed by the dyadic gap.
    - The naive quotient `ψ(ι_k s)/ψ(r_1)` for Farley's function grows like `4^k`, consistent with
      the dead end above.
  - *Open next step.* Decide (K). A positive answer proves this claim. For a negative answer
    one would look for an obstruction, for instance a bounded-cohomology or rotation-number
    invariant that vanishes on `V_T` but not on `e_R`.
- **2026-09-18 (swarm-0917-w13-w13-nv-break, calibration): the permanence-closure class dies.**
  - *Class-kill (established).* `lifted-thompson-t-escapes-haagerup-permanence-closure`.
    - Named invariant, three facts:
      - every normal subgroup of `T̄` is `⟨z^j⟩` or `T̄` (from simplicity of `T`);
      - `T̄` has no finite quotients;
      - the central `z` has roots of every order.
    - Death step: the first permanence operation pulls `T̄` back into one of its inputs:
      - finite product: into a factor;
      - restricted wreath `Γ ≀_X G`: into `Γ` or `G`, and always into `G` when `Γ` is abelian;
      - finite-edge graph of groups: into a vertex group;
      - extension with amenable quotient: into the kernel;
      - directed union or finite-index overgroup: into a member.
      By induction `T̄` then reaches a building block, where it dies:
      - amenable blocks, since `T̄` is nonamenable;
      - blocks with a proper commensurating action (cubical, Farley), since `z` is elliptic;
      - amenable-by-(residually finite or linear) blocks, since `T̄` has no residually finite
        image.
    - Killed: every proof of this claim, or of `nV` Haagerup through `T̄`, by embedding into a
      permanence construction. This includes Brothier-type `K ≀_{Q_2} V` hosts, amalgams over
      finite groups, and linear, Lie or residually finite hosts with amenable kernels.
  - *Sharpness.* The two operations left out are exactly the escapes:
    - central extensions, since `T̄` is one over `T`;
    - countable unrestricted products, since `T̄ ↪ ∏_k T` through the maps `ι_k` of
      `lifted-thompson-t-quotients-are-rotation-centralizers`.
    So a proof must build a new cnd function that is proper on `⟨z⟩`, at the Euler class or in a
    residual limit of `T`-representations.
  - *Correction.* `T̄ ⊇ Z[1/2]`, so by Higman (verbatim in
    `hall-quotient-avoids-v-circle-groups-and-periodic-ends`) `T̄` is not a subgroup of `V` at
    all. The frontmatter wording is updated to match.
- **2026-09-19 (swarm-0917-w14-w14-nv-last1, local-designs): step (b) dies for every weight.**
  - *Result (ESTABLISHED, `thompson-boundary-density-forms-are-extractable`).* Every
    `π_λ`-invariant Hermitian form on `θ`-quasi-periodic dyadic step functions,
    `F ↦ (g^{-1})'^λ F∘g^{-1}`, is classified, for all `λ ∈ C` and all `θ`:
    - `0` for generic `λ`;
    - a multiple of Lebesgue `∫_0^1 FḠ` when `Re λ = 1/2`;
    - a real multiple of an explicit kernel `B^1_θ` when `λ ≡ 1`; it is indefinite for `θ ∉ Z`
      and equal to `|mass|²` for `θ ∈ Z`;
    - jump forms at dyadic points when `λ ≡ 0`.
  - *Mechanism.* For fixed `Q`, invariance and the two-children relation give
    `φ_I = 2^{1−λ} φ_I` and `φ_{L,R} = 2^{-λ}(φ_{L,R} + φ_I)`. Here the subscripts are the
    edge types of a normalized brick in the complement of `Q`. On the diagonal,
    `c = 2^{1−2Re λ} c`.
  - *Consequence.*
    - The complementary-series weights `0 < |s| < 1/2` carry no nonzero invariant form at all.
    - Every positive form gives a twisted Koopman, jump-orbit (`ℓ²` of `Z[1/2]`) or trivial
      representation. The first two have covariant PVMs on `S^1`.
    - So all cocycles into their direct sums are bounded on `⟨z⟩`, by
      `lifted-thompson-t-extractable-cocycles-bounded-on-centre`.
    - The same classification holds for `nV` on `C^n`, and there only Koopman or trivial
      representations occur.
  - *Forced shape (sharpened).* A witness for this claim cannot come from any density weight on
    a single boundary point. What remains open is configuration spaces of `k ≥ 2` boundary
    points with non-convex kernels, and non-locally-constant models such as Ptolemy–Thompson.
  - Unchanged: this does not decide the claim, which stays OPEN.
- 2026-09-19 (swarm-0917-w15-w15-nv-break, stability-approximation): the order-type
  configuration class dies. Status stays OPEN.
  - *Class-kill (established).* `lifted-thompson-t-order-type-kernels-bounded-on-centre`, proved
    by `lifted-thompson-t-order-type-kernels-riesz-smear-proof`.
    - (O1) Every cnd function on `T̄` that is bi-invariant under `Stab(0) ≅ F` is bounded on all
      of `T̄`.
    - (O2) Every cnd function bi-invariant under the pointwise stabilizer `H_Y` of a finite
      periodic dyadic configuration `Y` of depth `d` has `sup_n ψ(z^n) <= 4ψ(r_{d+1})`.
    - Named invariant: order type is `Homeo~+(S^1)`-invariant, so it is unchanged by real
      translations.
    - Death step: smearing along translations gives a step-function cnd on `R`. By
      Riesz–Crum, `e^{-sφ}` is a.e. continuous, so the winding steps `floor(y − x)` vanish.
  - *Killed.*
    - The unit-interval metric `ceil|x − y|` (already not of negative type at 2 generic points per unit on `[0, 6)`).
    - Every function of `floor|x − y|`.
    - All walls, convex or not, spanned by configuration points. This subsumes the w9
      order-convex kill on its point-kernel part.
    - Schreier-graph and separating-point kernels on `T̄/H_Y`.
    - Sums of any of these at bounded depth.
  - *Quantitative test for the residual route (O3).* A sum `Σ ψ_i` of configuration kernels, for
    example `Σ a_k ψ_k∘ι_k` with `ψ_k` order-type on `T`, is proper on `⟨z⟩` only if
    `Σ_i ψ_i(r_{d_i+1}) = ∞`. So the depths must be unbounded, and the mass must escape to depth.
  - *Calibration.* `experiments/tbar-order-type-kernels-2026-09-17/check.py`. A 5% jump at
    distance 1 first fails at density 64 per unit length. This matches `N ≈ 1/(0.43 ε)`, and it
    explains why sparse tests look fine.
  - *Forced shape.* A survivor reads non-order-type data: slopes or caret structure (Farley-type
    parametrized intervals, whose pair orbits are not `Homeo~`-traces), measure-class data, or
    a depth-escaping infinite sum.
