---
rg: 2
id: fp-simple-finite-group-models-reduce-to-alternating-constituents
kind: claim
title: Finite-group hyperlinear models of a finitely presented infinite simple group reduce to alternating constituents
distinct_from:
  template-constituents-primitive-or-small-minimal-degree: that is the established reduction to primitive irreducible representations and primitive permutation groups of vanishing relative minimal degree; this is the open identification of both branches as alternating type
  fp-simple-groups-have-no-classical-group-unitary-models: that excludes one family of targets outright; this asks for the positive template identifying what any model must contain
---

**OPEN.** Let `S` be a finitely presented infinite simple group with a finite-group hyperlinear (or sofic) model, as on
`fp-simple-models-concentrate-on-template-constituents`. Take thresholds `θ_k → 1` along `ω`. The template constituents carry
definite weight and should be of *alternating type*:
- **(M) induced branch.** The primitive permutation groups of degree `→ ∞` and relative minimal degree `→ 0` from
  `template-constituents-primitive-or-small-minimal-degree` have socle `A_m^ℓ` with `m → ∞`, in product action on `ℓ`-tuples
  of subsets.
- **(P) primitive branch.** Primitive irreducible representations in which some relator is non-scalar with ratio `→ 1`. Here
  the expected form is that the generalized Fitting layer of the image has an alternating component of unbounded degree on which
  a relator acts non-scalarly. The precise form is part of the question.

The permutation case is the sofic template. Alternating constituents cannot be excluded in general, because sofic groups have
permutation models in `Sym(n)`.

## Attempts

- **Template reduction (established, unreviewed, lane sk-trace-template, 2026-09-13).**
  - `fp-simple-models-concentrate-on-template-constituents`: models concentrate on large irreducible constituents where the
    relators are non-scalar but nearly scalar.
  - `constituent-gapped-finite-groups-closed-under-products` and `fp-simple-groups-have-no-models-through-classical-products`:
    products and quotients of quasisimple classical and abelian groups give nothing, even over bounded-depth derived towers.
  - `template-constituents-primitive-or-small-minimal-degree`: induced constituents and orbits push down to primitive sections
    with `μ̂ → 0`.
- **(M) branch: minimal-degree classification, recalled, not imported.**
  - The expected input is the classification of primitive permutation groups of small minimal degree: Liebeck–Saxl, *Minimal
    degrees of primitive permutation groups, with an application to monodromy groups of covers of Riemann surfaces*,
    Proc. LMS (3) 63 (1991) 266–314, doi:10.1112/plms/s3-63.2.266; Guralnick–Magaard, *On the minimal degree of a primitive
    permutation group*, J. Algebra 207 (1998) 127–145, doi:10.1006/jabr.1998.7451.
  - Metadata checked on Crossref (2026-09-13). The theorem statements were not read: both publisher PDF requests from MSI
    returned HTML, and the arXiv API was rate-limited.
  - Recalled content (unverified): apart from bounded exceptions, a primitive group of relative minimal degree below `1/3`
    (Liebeck–Saxl) or `1/2` (Guralnick–Magaard) lies in `S_m ≀ S_ℓ` in product action, with socle `A_m^ℓ` acting on
    `ℓ`-tuples of `k`-subsets.
  - A `-citation` route with the verbatim statement would settle (M) as alternating type, with `m → ∞` forced by degree `→ ∞`.
- **(P) branch: open.**
  - Clifford theory makes every normal subgroup of the image act homogeneously, and the generalized Fitting subgroup is a central
    product of an extraspecial-type layer and components permuted by the top.
  - What is needed is a character-ratio gap at non-scalar elements for primitive irreducible representations whose layer has
    no alternating component of unbounded degree.
  - Known inputs: the quasisimple classical components are gapped (`lst-quasisimple-classical-character-ratio-bound`), and noncentral
    elements of an extraspecial layer of order `p^{1+2m}` have character value `0` in its faithful irreducible
    representation (standard).
  - Not handled: elements of the top group acting on tensor-induced layers, where normalized traces of factor permutations are
    small but the bound must be uniform, and exceptional or sporadic components, where a Gluck-type ratio bound is recalled
    but not read.
- **Why alternating constituents stay.** Every sofic group has permutation models in `Sym(n)`. An f.p. infinite simple sofic
  group, if one exists, therefore has models whose constituents are standard representations of alternating groups. The
  reduction can at best identify alternating type; it cannot rule it out.
