---
rg: 2
id: full-shift-full-group-has-infinite-normal-relative-t-subgroup
kind: claim
title: "Some subgroup of the full-shift topological full group has an infinite normal subgroup with relative property (T), necessarily locally finite, for instance a copy of EL_2(F_p[t,t^-1]) ⋉ F_p[t,t^-1]^2"
distinct_from:
  wobbling-normal-relative-t-subgroups-are-locally-finite: that proves any such normal subgroup is locally finite; this asks whether an infinite one exists at all
  full-shift-topological-full-group-is-a-t-menable: that is the Haagerup property of [[X]]; this claim, if true, refutes it, and its negation is only the normal-pair part of that property
  elementary-linear-semidir-pair-relative-t: that gives the relative-(T) pairs; this asks whether one with a locally finite base lives inside [[X]]
---

**OPEN.** `X = {0,1}^Z` and `[[X]]` its topological full group.

**Statement.** There are `Γ ≤ [[X]]` and an infinite `H ⊴ Γ` such that `(Γ, H)` has relative
property (T).

## Role

- If true, `[[X]]` is not Haagerup: a Haagerup group has no relative-(T) pair with an infinite
  subgroup. That refutes `full-shift-topological-full-group-is-a-t-menable`, and through
  `full-shift-full-group-a-t-menable-from-nv` it refutes `brin-thompson-groups-nv-are-a-t-menable`
  for every `n ≥ 2`.
- If false, the normal-pair refutation route is closed, and any refutation of the Haagerup
  property of `[[X]]` needs a non-normal relative-(T) subset.

## Forced shape

By `wobbling-normal-relative-t-subgroups-are-locally-finite`:
- `H` is locally finite. It contains no element of infinite order, and no infinite finitely
  generated subgroup.
- A finitely generated `H' ≤ H` whose generators have jumps at most `c` has all its orbits on each
  aperiodic `σ`-orbit bounded by `2 max(L_0, 2c)`.
- On every aperiodic orbit, every window of length `L ≥ L_0` has at most a `2δ²` fraction of
  points whose `H`-orbit is larger than `2L`.

By `subexponential-schreier-growth-excludes-sl3z-and-bs1k`, no infinite-order element of a finitely
generated subgroup of `Γ` is exponentially distorted.

## Candidate

The natural candidate is `Γ_p = EL_2(F_p[t, t^{-1}]) ⋉ F_p[t, t^{-1}]²` with `H` the base. The pair
has relative (T) by `elementary-linear-semidir-pair-relative-t`, and the base is an infinite
elementary abelian `p`-group, so the forced shape above does not exclude it.
- Whether `Γ_p` is residually finite and whether its infinite-order elements are undistorted have
  not been checked here. Both are necessary conditions, by
  `full-shift-topological-full-group-is-residually-finite` and the distortion bound.
- A first falsifiable test: does `Γ_p` act faithfully on `Z` by bounded-displacement bijections at
  all, that is, does `Γ_p` embed in `W(Z)`?

## Attempts

- **2026-09-19 (swarm-0917-w17-w17-nv-last1): Salo lamplighter realizations of the base (no
  witness yet; deferred).**
  - Salo (arXiv:2103.06663) embeds `A ≀_Ω G` in `[[X]]` when `G ≤ [[X]]` acts on `Ω` with suitable
    moves. The resulting base modules are quotients of `A[G]` that embed in products of
    permutation modules `A[G/G_x]` over points `x`.
  - For the plain orbit module, the point-indicator characters form a `G`-set of linear growth,
    since `W(Z)`-orbits have linear growth. That `G`-set is amenable, so the permutation
    representation on it has almost invariant vectors and no base-invariant vector. So the plain
    orbit module never has relative (T). This was checked in outline, not written as a node.
  - To realize `F_p[t,t^{-1}]²` with relative (T), the characters of the base must avoid every such
    amenable orbit family. By `elementary-linear-semidir-pair-relative-t`, the character space of
    `F_p[t,t^{-1}]²` carries no `EL_2`-almost-invariant probabilities near `0`.
  - So a realization needs a submodule whose dual sees no point-indicator characters. It is not
    known whether Salo's construction can produce one.
  - **Next falsifiable step:** decide whether `Γ_p` embeds in `W(Z)` at all. For example, test
    whether its Schreier graphs on some faithful action can have bounded bandwidth.
- **2026-09-19 (swarm-0917-w18-w18-nv-pull): the bandwidth test, done in general.** See
  `wobbling-tau-subgroups-need-coamenable-infinite-index-subgroup`.
  - Items 1–3 are established by `wobbling-tau-coamenable-proof`.
  - *Bounded crossing.* `H`-orbits cross every cut boundedly often, at every scale.
  - *Finite orbits.* A (τ)-group in `W(Z)` has finite orbits of size at most `16r/κ²`: an expander
    gap contradicts the bounded median cut of a finite orbit.
  - *Infinite orbits.* Hence an infinite (τ)-subgroup of `W(Z)` has infinite-index co-amenable
    point stabilisers.
  - *For `Γ_p`.* The following is conditional on (τ) for `SL_2(F_p[t,t^{-1}])`, recalled from
    Serre's CSP with `|S| = 2` and Drinfeld's congruence gap, and not checked verbatim. Under that
    assumption, `Γ_p ↪ [[X]]` needs **(P)**: a non-amenable, infinite-index, co-amenable subgroup of
    `SL_2(F_p[t,t^{-1}])` that stabilises a finite-codimension subspace of `F_p[t,t^{-1}]²`.
  - *Consequence.* Bounded bandwidth for finite quotients is impossible. Any embedding must go
    through amenable infinite Schreier graphs of `Λ`. If (P) fails, the candidate is dead.
- **2026-09-19 (swarm-0917-w19-w19-nv-pull): the candidate `Γ_p` is refuted; it does not embed in
  `W(Z)`.** See `laurent-elementary-semidirect-product-is-not-in-wobbling-group`, established by
  `laurent-elementary-semidirect-not-in-wobbling-proof`. Every `ρ: Γ_p → W(Z)` kills an infinite
  subgroup of the base. Where each part of the argument does its work:
  - **Relative (T) makes base orbits finite.** Relative (T) plus normality gives a uniform
    `(Q, κ)`. Testing it on `1_J` for intervals `J` shows that every `H`-orbit is finite.
  - **(τ) bounds the finite `Γ`-orbits.** On a finite orbit, the half-indicator vector is
    `O(1/n)`-invariant. Relative (T) pushes it into `ℓ²(O)^H ≅ ℓ²(O/H)`. There, (τ) of `SL_2(R)`
    for all finite-index subgroups caps `n`. That (τ) comes from Serre's finite congruence kernel
    (`|S| = 2`) plus the Drinfeld Selberg property.
  - **Congruence on the infinite orbits.** There are at most `2r` infinite orbits. On each one,
    the `u_s` for `s ∈ span{t^{2k} : |k| ≤ N}` would produce `p^{2N+1}` characters inside a
    Schreier ball of linear size. So a nonzero ideal `I` has `I R²` acting trivially there.
  - Cornulier's FW theorem does not apply, since `E` fails FA.
- **Class kill.** Take any `(Γ, H)` with relative (T), `H ⊴ Γ`, and `Γ/H` with (τ) for all
  finite-index subgroups. In any bounded-displacement action, `Γ` acts through a finite quotient
  on `Z_fin`, and `H` is seen faithfully only on at most `2r` infinite orbits, with finite
  `H`-orbits there. So:
  - arithmetic quotients over module bases `R^n` with a contracting diagonal element are dead;
  - a surviving witness needs `Γ/H` without (τ) on its finite-index subgroups, or a base whose
    character orbits on one infinite `Γ`-orbit grow at most linearly under the `Γ/H`-action.
  - Linear growth of character orbits under `Γ/H` is an amenability-type condition. It pulls
    against relative (T), in the way the w17 lamplighter observation above does.
- **Next falsifiable step:** decide whether a relative-(T) pair with a locally finite base can have
  `Γ/H`-orbits on `Ĥ` of linear growth near the trivial character, or show that relative (T)
  forces exponential growth there. The second would close this claim negatively for all `Γ/H`
  with (τ).
- **2026-09-19 (swarm-0917-w19-w19-nv-last1): the named candidate `Γ_p` is excluded from `W(Z)`
  modulo one import (class-kill of every realization of `Γ_p`).**
  - *New forced shape (ESTABLISHED).* `wobbling-normal-relative-t-subgroups-have-bounded-displacement`
    shows that every element of `H` has displacement `< B = ⌊24D²/ε²⌋ + 1`, with `(Q, ε)` a Kazhdan
    pair and `D` the maximal displacement on `Q`. So every `H`-orbit has at most `2B − 1` points,
    and `H` has finite exponent. The proof uses a tent vector against the normal Kazhdan
    projection. It needs no finite generation. This strengthens the window bound quoted above.
  - *Invariant.* The point-kernel map `x ↦ K_x = Stab_M(x)`. By the bound, it takes values in
    subgroups of index `≤ 2B − 1`, and it is `Γ_p`-equivariant for the `E`-action on subgroups of
    `M`.
  - *Unconditional theorem (ESTABLISHED).* `burger-laurent-pair-wobbling-point-kernels-are-congruence`
    shows that in every embedding `Γ_p ≤ W(Z)`:
    - every `E`-orbit `Q_x` of point kernels is finite;
    - it is a quotient of a congruence quotient `E/E(I_x)`, `I_x ≠ 0`;
    - the sizes `|Q_x|` are unbounded;
    - pushing interval windows of `Z` through the kernel map gives, in each `Q_x`, sets of every
      size with boundary `≤ 2D_S`.
  - *How infinite orbits die.* The stabilizer of a finite-index `K` with an infinite orbit fixes a
    non-torsion character `(α, β)` of `M`. Over `F_p(t)` that stabilizer is trivial or unipotent,
    so `Stab_E(K)` is virtually abelian. The windows make it co-amenable, which would make `E`
    amenable. That contradicts relative (T).
  - *Where every member dies.* A realization of `Γ_p` in `W(Z)` or `[[X]]`, by lamplighters,
    Salo-type constructions or anything else, would make congruence Schreier graphs of
    `SL_2(F_p[t,t^{-1}])` of unbounded size have Cheeger constant `O(1/size)`. The Selberg property
    forbids this (`burger-laurent-pair-not-in-wobbling-group-from-selberg-proof`).
  - *Status.* `burger-laurent-pair-is-not-in-the-wobbling-group` stays OPEN with exactly one open
    prerequisite, `laurent-sl2-positive-characteristic-has-selberg-property`. That prerequisite is
    Drinfeld-based (τ) for all congruence levels. Lubotzky's survey (arXiv:1105.2389, §2.4) states
    it in prose, and only explicitly for the prime levels.
  - *Consequence for this claim.* Once the import lands, a positive answer needs a pair other than
    `Γ_p`. The argument uses:
    - `R` a finitely generated domain of characteristic `p`: Claim 6.1 and the finiteness of
      bounded-index ideals;
    - a spectral gap for the congruence quotients of `EL_2(R)`.
    So the natural next candidates, `EL_2(R) ⋉ R²` over other such `R`, die in the same way
    wherever the Selberg property is known. A surviving pair must have a base whose point-kernel
    orbits are finite, non-congruence, or non-expanding.
- **2026-09-19 (swarm-0917-w19-w19-nv-follow): R-core rank of point stabilisers (class kill for
  rank-two affine witnesses with (τ); the claim stays OPEN).**
  - `rank-two-affine-relative-t-pairs-in-wobbling-groups-fail-tau` is ESTABLISHED by a
    self-contained route. Its setting: `R` is any infinite commutative domain, `Λ ≤ GL_2(R)` is
    arbitrary, `Γ = Λ ⋉ R²` is finitely generated, and `(Γ, R²)` has relative (T).
  - For every bounded-displacement action of such a `Γ` on `Z`:
    - some `dR²` with `d ≠ 0` acts trivially on every orbit, finite or infinite;
    - faithfulness forces unbounded finite orbits `O` on which `Λ` has no uniform spectral gap on
      the `Λ`-sets `O/A`.
  - So no such pair with `Λ` having (τ) lives in `W(Z)` or `[[X]]`.
  - Key step: the stabiliser in `Λ` of a finite-index `V ≤ R²` is virtually metabelian unless the
    largest `R`-submodule inside `V` has rank two. Relative (T) makes that stabiliser co-amenable
    and makes `Λ` non-amenable.
  - This removes the need for a contracting diagonal element or an exponential-growth estimate on
    characters. Every earlier argument for the named candidate used one of these, as did the class
    kill recorded in wave 19 by w19-nv-pull, which is not yet on this branch.
  - The named candidate `Γ_p` falls under it once (τ) for `SL_2(F_p[t,t^-1])` is imported, and
    that import is not recorded here with a verbatim citation.
  - **Where a witness must now live.** Take `H` abelian with a rank-two module structure over a
    domain. Then `Γ/H` must fail (τ), precisely along the finite `Λ`-sets `O/A`, which lie over
    congruence quotients `Λ ⋉ (R/dR)²`. Otherwise `H` needs rank at least 3, or is not a
    torsion-free module over a domain.
  - For rank `n ≥ 3` the rank lemma leaves a stabiliser containing `GL(W)`, which is not amenable.
    The obstruction then needs co-amenability input on `Λ`.
  - **Next falsifiable step:** find a finitely generated `Λ ≤ SL_2(R)`, `R` an infinite domain of
    characteristic `p`, with `(Λ ⋉ R², R²)` relative (T), and with a family of finite quotients
    `Λ ⋉ (R/d_jR)²` whose Schreier graphs have bounded bandwidth. Or show that relative (T) of the
    pair forces (τ) on congruence quotients of `Λ`.
- **2026-09-20 (swarm-0917-w21-w21-nv-last1): class kill by Property FM of the quotient
  (ESTABLISHED as `wobbling-relative-t-pairs-with-fm-quotient-are-finite`).**
  - Invariant: Cornulier's Property FM of `Γ/H`.
  - Step where every member dies. `Γ → Γ/H` is a Kazhdan homomorphism (Cornulier 1308.1318,
    Ex. 2.7), so FM lifts to `Γ` (Thm 6.12). Then Thm 7.1(2) gives finite image in `W(Z)`, hence in
    `[[X]]`.
  - So every witness has `Γ/H` non-amenable and without FM. This kills quotients with (T), (T)-factor
    lattices (Thm 1.13, including non-FA ones), and FM-by-FM extensions.
  - For `Γ_p` it gives only a conditional kill: `SL_2(F_p[t,t^-1])` would have to lack FM, which is open
    (a tree-product case of the hard case of Conjecture 1.10). The unlanded w19 `(τ)` argument is the
    stronger kill of `Γ_p`.
  - Survivors: quotients without FM, e.g. non-amenable groups with an amenable action without finite
    orbits.
- **2026-09-20 (swarm-0917-w23-w23-nv-break): a free linear part is enough for relative (T) (new
  witness class; no embedding yet).**
  - `char-p-burger-pairs-for-nonamenable-subgroups-of-sl2-fq-t` (ESTABLISHED in this lane, not
    reviewed) proves that `(Λ ⋉ F_q[t]², F_q[t]²)` has relative (T) for *every* non-amenable
    `Λ ≤ SL_2(F_q[t])`, and in particular for a free `F ≤ SL_2(F_q[t])`. The route is Burger's: an
    invariant mean on `P¹(F_q((1/t)))`, then the amenable boundary action of the Bruhat–Tits tree.
  - So a copy of `F ⋉ F_q[t]²` in `[[X]]` suffices. It is a subgroup of `Γ_p`, so it is a strictly
    weaker target than `Γ_p`. Its base is locally finite, as the forced shape requires.
  - Its quotient `F` fails (τ) and fails property FM. So the wave 18–21 class kills that need a (τ)
    or FM quotient do not reach it (live-bus nodes, not in this worktree).
  - The rank-two affine kill of wave 19 still applies when `F ⋉ F_q[t]²` is finitely generated. It
    then asks for a uniform spectral gap of `F` on congruence-type finite quotients, which is a
    super-strong-approximation question for thin subgroups of `SL_2(F_q[t])`. The countable version,
    with `F_q[t]²` not finitely generated as an `F`-module, is outside that kill.
  - Not established: relative (T) for a finitely generated `F`-submodule `N ⊂ F_q[t]²` of infinite
    index. The proof above uses that `M` is all of `R²`, through duality with `K²/R²`.
  - **Next falsifiable step:** embed the countable group `F ⋉ F_q[t]²` in `W(Z)`, or in `[[X]]`, by a
    one-sided linear-CA lamp realization over `(F_p²)^N`, in the manner of the lifting criterion of
    `char-p-burger-lamp-realizations-refute-haagerup`, with the linear part only free.
    Alternatively, show that every faithful bounded-displacement action of it has amenable
    character orbits near `0`.
