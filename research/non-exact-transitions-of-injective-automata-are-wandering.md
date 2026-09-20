---
rg: 2
id: non-exact-transitions-of-injective-automata-are-wandering
kind: claim
title: One-way letter transitions of an injective automaton happen only on wandering cylinders, so no invariant measure or periodic point sees them, while a never-created letter's destruction is always visible on quiescent finite configurations
distinct_from:
  injective-automata-with-inter-class-transitions-are-strict: that proves bijective automata have only exact upsets, using invariance of the uniform product measure, and deduces strictness from one inter-class arc; this proves that for every injective automaton each non-exact event sits on a wandering cylinder, so exactness holds on the whole nonwandering set and on the support of every invariant measure, and shows that measure invariance cannot be pushed past bijective automata to decide whether never-created letters are inert.
  finite-injective-charge-noncreation-forces-surjectivity: that forbids an injective automaton with a quiescent symbol from lowering a positive charge on finite configurations; this shows that a never-created, sometimes destroyed letter is quiescent and raises the opposite charge (the number of non-quiescent sites) on some finite configuration, so the cofinite branch of the wave-20 dichotomy is exactly a charge-creating injective automaton.
  strict-automaton-upsets-give-smaller-nonsurjunctive-sizes: that descends strictness along upsets; this locates the sites where an upset is entered one way, dynamically.
  compressible-base-controlled-automata-are-strict: that is a calibration by compression swindles over a Cantor base; this is a statement about ordinary automata on the full shift and uses no base.
artifacts:
  - research/wandering-destruction-cylinder-proof.md
---

**ESTABLISHED** by `wandering-destruction-cylinder-proof`, over every group. Elementary. The only import is
`bijective-ca-preserve-uniform-bernoulli-measure`, used for item 1(b).

**Setting.** `G` is any group, `B` a finite alphabet, `Φ(x)(g) = μ((g^(-1)x)|_M)` a cellular automaton on
`B^G` with `1 ∈ M` finite. `R(Φ)`, upsets and exact upsets are as in
`injective-automata-with-inter-class-transitions-are-strict`. For an upset `U`, a *non-exact event* of `Φ` at
`g` in `x` is `x(g) ∉ U` and `Φ(x)(g) ∈ U`. It depends only on `x|_(gM)`. A pattern `P ∈ B^M` with
`P(1) ∉ U` and `μ(P) ∈ U` is a *non-exact pattern*, and `[P]_g = {x : (g^(-1)x)|_M = P}` is its cylinder
at `g`.

A point `x` is *wandering* if some open `V ∋ x` has `Φ^k(V) ∩ V = ∅` for every `k >= 1`. `NW(Φ)` is the
closed set of nonwandering points.

**Theorem.** Let `Φ` be injective on `B^G`.
1. **Wandering is strictness.**
   - (a) `NW(Φ) ⊆ Φ(B^G)`.
   - (b) `Φ` is surjective if and only if `NW(Φ) = B^G`.
   - (c) So `G` is surjunctive if and only if every injective automaton over `G` is nonwandering.
2. **Non-exact events wander.** Let `U` be an upset of `R(Φ^p)` for some `p >= 1`, and `P` a non-exact
   pattern of `Φ^p` for `U`. Then:
   - (a) `Φ^(pk)([P]_g) ∩ [P]_g = ∅` for all `k >= 1` and all `g`.
   - (b) Every point of `[P]_g` is wandering for `Φ^p`. So every upset `U` of `R(Φ^p)` is exact on
     `NW(Φ^p)`: `x ∈ NW(Φ^p)` gives `x(g) ∈ U ⇔ Φ^p(x)(g) ∈ U` for all `g`. For `p = 1` this is exactness of
     every upset of `R(Φ)` on `NW(Φ)`.
   - (c) `ν([P]_g) = 0` for every Borel probability measure `ν` with `Φ_* ν = ν`. This includes every
     weak-* limit of Cesàro averages `(1/K) Σ_(k<K) Φ^k_* λ`, for any starting measure `λ`. So no
     non-exact pattern occurs in any configuration of the support of any `Φ`-invariant measure.
   - (d) No non-exact pattern occurs in any configuration with finite `Φ`-orbit. In particular none occurs
     in any `H`-periodic configuration, for any subgroup `H` of finite index in `G`.
3. **Never-created letters are quiescent and create charge on finite configurations.** Let `c` be never
   created by `Φ`, so `A = B \ {c}` is an upset. Then:
   - (a) `Φ(c^G) = c^G`, i.e. `μ(c^M) = c`.
   - (b) `Φ` maps the set `X_fin` of configurations with finitely many `A`-sites into itself. On `X_fin`,
     `W(x) = |{g : x(g) ∈ A}|` satisfies `supp_A(x) ⊆ supp_A(Φ x)`, so `W(Φ x) >= W(x)`.
   - (c) If `c` is destroyed in some context `P ∈ B^M`, then `P` padded with `c` outside `M` is a point `x`
     of `X_fin` with `W(Φ x) > W(x)`.
   - (d) So the cofinite branch of item 4 of `injective-automata-with-inter-class-transitions-are-strict` is
     non-empty over `G` if and only if some injective automaton over `G`, with a quiescent symbol `c` that
     it never creates, raises the number of non-`c` sites of some finite configuration. That is the
     reverse of the inequality excluded by `finite-injective-charge-noncreation-forces-surjectivity`, for
     the charge `1` on every non-quiescent letter.
4. **Garden-of-Eden filling.** In the setting of item 3, put `τ = Φ|_(A^G)` and `Y = τ(A^G)`. If `x` has a
   nonempty set of `c`-sites and `Φ` destroys `c` at every one of them, then `Φ(x) ∈ A^G \ Y`. So every
   configuration whose holes are all filled in one step lands in the Garden of Eden of `τ`.

**What this kills.** The wave-20 dichotomy leaves one question that decides whether `NS(G)` can be cofinite
by the singleton-class route: *is every never-created letter of an injective automaton inert?* Item 2 shows
that two families of attack cannot decide it, in either direction.
- **Measure invariance past bijectivity (entropy-measure).** The wave-20 proof of inertness for bijective
  `Φ` uses one invariant measure of full support, the uniform product measure. For injective `Φ` that is
  not onto, no invariant measure has full support: its support lies in `NW(Φ)`, which by item 1(a) lies
  in `Φ(B^G) ≠ B^G`. By 2(c) every invariant measure gives the destruction cylinders mass `0`. This
  includes Cesàro limits of the orbit of the uniform measure, entropy-maximising measures, and measures
  on the limit set.
  - An argument whose only input is a `Φ`-invariant measure therefore sees an injective automaton
    exactly as it sees a bijective one, as far as letter transitions go. It can neither exclude a
    destroyed letter nor certify one.
  - *Dying step:* one needs an invariant measure charging `[P]_1`, and there is none.
- **Periodic and finite-quotient certificates (census-computation, finite-models).** By 2(d) a destruction
  pattern never occurs in an `H`-periodic configuration with `[G : H] < ∞`. The same holds for any
  non-exact pattern of any upset of any power.
  - A search on a finite quotient `G/H` cannot exhibit a witness: the induced map on `B^(G/H)` is a
    bijection with exact upsets.
  - Over a residually finite group, every pattern extends to a periodic configuration, so non-exact
    patterns do not exist at all. This agrees with Gromov–Weiss and adds nothing there.
  - *Dying step:* from periodic data to a cylinder that meets no periodic point.
- **What survives.** Any decision must be made on wandering configurations. There are two routes:
  - Garden-of-Eden-type counting on the finite configurations of item 3, which is the dual of
    `finite-injective-charge-noncreation-forces-surjectivity`.
  - Constructions that fill holes into the Garden of Eden of the strict core, as item 4 requires.

**Why it matters.**
- Item 1 recasts the conjecture as *every injective automaton is nonwandering*. Item 2 shows that the
  sitewise certificates of strictness known so far are all wandering cylinders of one kind. Those
  certificates are the inter-class arcs of wave 20 and the non-exact upsets. Strictness is the existence
  of some wandering open set, and these are the ones that can be read off the local rule.
- Item 3 turns the cofinite branch into a statement about countably many finite configurations over a
  quiescent background. A witness is precisely a *charge-creating* injective automaton: finite charge
  destruction is already excluded, and finite charge creation is the only freedom a strict encoder has,
  as the charge-noncreation node notes.
- Item 4 is a necessary design constraint for the one-letter ascent `k -> k + 1` by a never-created
  letter. Such an ascent is automatically strict by wave-20 item 6, and it forces cofinite `NS(G)`. The
  constraint is that configurations whose holes all fill at once must be sent injectively into
  `A^G \ τ(A^G)`, so the extension must spend the core's Garden of Eden.

**Where it stops.**
- Nothing here decides whether a charge-creating injective automaton exists over some group. The dual of
  the charge-noncreation theorem, *an injective automaton with a quiescent never-created symbol never
  raises the non-quiescent count of a finite configuration*, is open. It is equivalent to the inertness of
  every never-created letter over `G`.
- The kill applies to arguments that use only invariant measures or periodic data. The uniform product
  measure `λ` itself is not invariant and does charge `[P]_1`: `(Φ_* λ)([c at 1]) < λ([c at 1])`. An
  argument that tracks the non-invariant orbit `Φ^k_* λ` is not covered.
- No calibration world is given in which a witness exists. The claim that these families "cannot decide"
  the question is the statement that their data coincide with those of a bijective automaton. It is not
  an independence result.
