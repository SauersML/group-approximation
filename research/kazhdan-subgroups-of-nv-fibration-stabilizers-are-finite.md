---
rg: 2
id: kazhdan-subgroups-of-nv-fibration-stabilizers-are-finite
kind: claim
title: Every Kazhdan subgroup of nV that maps the fibres of a coordinate projection C^n -> C^I onto fibres, or of a conjugate of that stabilizer, is finite
distinct_from:
  kazhdan-subgroups-of-brin-thompson-groups-are-finite: that asks finiteness for all Kazhdan subgroups of nV; this settles it for subgroups preserving a coordinate fibration up to conjugacy, so an infinite Kazhdan subgroup must virtually preserve no such fibration.
  thompson-v-has-haagerup-property: that is the case n = 1 through a proper affine action; this inducts on n through the base map to |I|V and the locally constant fibre maps into |J|V, using the n = 1 case as the base.
  fw-subgroups-of-eventually-similar-groups-virtually-embed: that virtually embeds FW subgroups of one-shift similarity groups through commensurated cones; this uses no commensurated set, only the product structure of a preserved fibration.
artifacts:
  - research/artifacts/kazhdan-nv-displacement-gap-2026-09-17.md
---

**OPEN** for `n >= 3` (demoted 2026-09-18; see Attempts). The route
`nv-fibration-stabilizer-kazhdan-finite-proof` is complete only for `n = 2`, where the induction
bottoms out at `thompson-v-has-haagerup-property`. For `n >= 3` its induction invokes the
strictly stronger `kazhdan-subgroups-of-brin-thompson-groups-are-finite` for `m = |I|, |J| < n`,
which is OPEN for every `m >= 2`; that claim is now listed in the route's `requires:`. The honest
form of the statement is the conditional one, as in the sibling
`kazhdan-subgroups-of-fibred-subgroups-of-nv-are-finite`.

## Statement

For `n >= 2`, nonempty `I ⊊ {1,...,n}` with complement `J`, let `Stab_I <= nV` be the
elements `g` with `g({a} x C^J) = {v(a)} x C^J` for a bijection `v` of `C^I`. Every
Kazhdan subgroup of `h Stab_I h^{-1}` (`h ∈ nV`) is finite.

## Consequence for the target

An infinite Kazhdan `K <= nV` virtually preserves no `nV`-image of a coordinate fibration.
The decomposition "(T) forces a virtually preserved coordinate fibration" would prove
`kazhdan-subgroups-of-brin-thompson-groups-are-finite`, hence
`minimal-sets-of-kazhdan-subgroups-of-nv-carry-invariant-measures`; that prerequisite is
not claimed and can fail on its own. Details: artifact Section D.

## Attempts

- 2026-09-18 (adversarial referee pass, outcome refuted as stated, verdict f8533132): **the
  induction is circular and, at n = 3, asserts the open flagship claim.** Referee's reason,
  verbatim:
  - "Compiled status was ESTABLISHED via route nv-fibration-stabilizer-kazhdan-finite-proof
    [COMPLETE], whose only prerequisite is thompson-v-has-haagerup-property. The proof (artifact
    research/artifacts/kazhdan-nv-displacement-gap-2026-09-17.md, Section D, Prop D1; route steps 1
    and 3) is a circular induction. The statement being inducted is 'Kazhdan subgroups of Stab_I <=
    nV are finite', but step 1 ('the image of K is a Kazhdan subgroup of |I|V, finite by induction')
    and step 3 ('each coordinate projection of K_1 is a Kazhdan subgroup of |J|V, finite by
    induction') invoke the STRICTLY STRONGER statement 'every Kazhdan subgroup of mV is finite' for
    m = |I|, |J| < n. That statement is the claim kazhdan-subgroups-of-brin-thompson-groups-are-finite,
    which is [claim/OPEN] for every m >= 2, and nothing in the graph supplies it. Only m = 1 is
    available (Farley, thompson-v-has-haagerup-property). Hence the induction closes only at n = 2
    (where |I| = |J| = 1); step 3 is the first step that does not follow, first failing at n = 3.
  - Concretely the claim is not merely unproved but as strong as the open problem: for n = 3,
    I = {1}, J = {2,3}, Stab_{1} contains the whole subgroup {g : g(x_1,x_2,x_3) = (x_1,
    psi(x_2,x_3)), psi in 2V} = 1 x 2V (v = id, so it lies in Stab_{1}). So D1 at n = 3 literally
    asserts 'every Kazhdan subgroup of 2V is finite', i.e.
    kazhdan-subgroups-of-brin-thompson-groups-are-finite at n = 2. An ESTABLISHED claim therefore
    silently settles an OPEN flagship claim.
  - Corroboration from the graph: the sibling ESTABLISHED claim
    kazhdan-subgroups-of-fibred-subgroups-of-nv-are-finite treats the SAME group (Stab_I = Fib_I,
    since g({a} x C^J) = {v(a)} x C^J is exactly pr_I o g = v o pr_I) and states the correct
    CONDITIONAL form — 'Fib_J contains an infinite Kazhdan subgroup iff mV or (n-m)V does' — with
    unconditional conclusions only for n = 2 and for T_n, plus Corollary 4 restricting the fibration
    conclusion to a minimal counterexample n_0. The claim under review drops that hypothesis and
    asserts the unconditional version for all n >= 2.
  - Steps run: (0) synced origin/main, compiled status ESTABLISHED; (1) read claim file, route file
    and the artifact; (2) bin/cairn context confirms the only required prerequisite is
    thompson-v-has-haagerup-property [ESTABLISHED], and the needed m >= 2 prerequisite is absent
    (not merely mis-cited — never declared); (3) all three lenses applied; (4) no computation is
    asserted, so no script to run. Secondary checks that DID hold: g -> v is a well-defined
    homomorphism into |I|V; phi_a in |J|V and constancy on bricks of shape D_g; maps constant on a
    common refinement form a subgroup so K_1 <= Prod_{B in P} |J|V; quotients/finite-index
    permanence of (T) and f.g. of countable Kazhdan groups; conjugation invariance. Those are fine —
    the defect is solely the induction hypothesis. Correct honest status: the route is COMPLETE only
    for n = 2; the claim as stated (n >= 2) should be OPEN, or restated conditionally on
    kazhdan-subgroups-of-brin-thompson-groups-are-finite for all m < n. Verdict f8533132 posted with
    outcome refuted."
  - **The exact step that fails.** Step 3 of the route (= Prop D1 of the artifact), "each factor
    image is a Kazhdan subgroup of `|J|V`, finite by induction", first failing at `n = 3`.
  - **Demotion.** The missing statement is the existing open claim
    `kazhdan-subgroups-of-brin-thompson-groups-are-finite`, now listed in the route's `requires:`
    rather than duplicated as a new node. The proof file is kept: it is correct for `n = 2` and
    every step other than the induction hypothesis holds.
