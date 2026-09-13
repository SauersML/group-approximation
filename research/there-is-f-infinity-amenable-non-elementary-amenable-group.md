---
rg: 2
id: there-is-f-infinity-amenable-non-elementary-amenable-group
kind: claim
title: Some amenable group of type F_infinity is not elementary amenable
distinct_from:
  every-f-infinity-amenable-group-is-elementary-amenable: that is the opposite answer to Zaremsky 1.12, that no such group exists; this is the existence answer.
  fp-infinite-simple-amenable-group: that asks for a finitely presented infinite simple amenable group; this asks for an amenable non-EA group of type F_infinity, simple or not.
---

**OPEN.** There is a group that is amenable, not elementary amenable, and of
type `F_∞`. This is the construction answer to Zaremsky Problem 1.12
(`zaremsky-1-12-f-infinity-amenable-non-elementary-amenable`).

## Attempts

- **Grigorchuk's finitely presented HNN extension `G~` (candidate; open).**
  - `G` is the first Grigorchuk group. Lysenok's presentation has finitely
    many relators and their images under a substitution `σ`. Since `σ` induces
    an injective, non-surjective endomorphism of `G`, the ascending HNN
    extension `G~ = G *_σ` is finitely presented. Grigorchuk (1998) proves
    `G~` amenable and not elementary amenable. The relators and `σ` will be
    quoted from the source in a citation route.
  - Finiteness beyond `FP_2` is the open point. For trivial coefficients the
    Mayer–Vietoris sequence of the HNN extension reads
    `… → H_k(G) --(1 − σ_*)--> H_k(G) → H_k(G~) → H_(k−1)(G) → …`.
    `FP_3` needs, among other things, `ker(1 − σ_*)` on `H_2(G)` and
    `coker(1 − σ_*)` on `H_3(G)` to be finitely generated for every
    coefficient module, not only `Z`.
  - Fence (conditional on the bounded-orders half of Kropholler 1993, not yet
    read from the source). `G` is an infinite, finitely generated, residually
    finite 2-group, so by Zelmanov's solution of the restricted Burnside
    problem its exponent is unbounded. So `G~` has finite subgroups of
    unbounded order. If `G~` were of type `FP_∞`, the bounded-orders theorem
    would put `G~` outside `LH𝔉`. `G~` acts on its Bass–Serre tree with vertex
    stabilizers conjugate to `G`, so `G ∈ H𝔉` would give `G~ ∈ H𝔉`. Hence
    **`G~` of type `FP_∞` forces `G ∉ H𝔉`.** A proof of `F_∞` cannot run through
    a finite-dimensional contractible `G~`-complex whose stabilizers lie in
    `H𝔉`, e.g. Brown's criterion on the Bass–Serre tree.
- **Other finite endomorphic presentations (candidates; open).** Contracting
  regular branch groups have finite endomorphic presentations (Bartholdi,
  "Endomorphic presentations of branch groups", J. Algebra 2003). When the
  substitution is an injective endomorphism, the ascending HNN extension is
  finitely presented, and it is amenable when the base is, for instance for
  bounded automata groups (Bartholdi–Kaimanovich–Nekrashevych). The same fence
  applies to all of them. A weakly branch base contains products of `2^n`
  infinite rigid stabilizers for every `n`, so it has finite subgroups of
  unbounded order (torsion case) or `Z^(2^n)` for every `n` (torsion-free case,
  e.g. the Basilica group). In the torsion-free case a type-`FP_∞` extension
  has infinite cohomological dimension, so it lies outside `LH𝔉` by the
  verified torsion-free half of Kropholler's theorem (Januszkiewicz–
  Kropholler–Leary, arXiv:0908.3669v1, p. 1). In the torsion case the
  conclusion needs the bounded-orders half.
- **Topological full groups of minimal `Z`-subshifts (dead for the full group
  and its derived subgroup).** These groups are LEF (Grigorchuk–Medynets). A
  finitely presented LEF group is residually finite, and the derived subgroup
  is infinite and simple, hence not residually finite. So neither group is
  finitely presented; see also `periodic-approximable-subshifts-host-no-fp-simple-group`.
  Finitely presented amenable subgroups of such full groups are not ruled out.
- **Thompson's group `F` (conditional).** `F` is of type `F_∞` and not
  elementary amenable, so `thompson-f-is-amenable` implies this claim. A route
  will land once a node imports "F is of type F_∞ and not EA" with verified
  citations.
- **General fence (from Kropholler's theorem).** A torsion-free answer either
  lies outside `LH𝔉` or has finite cohomological dimension. No amenable non-EA
  group of finite cohomological dimension is known to this lane, so a
  torsion-free answer inside `LH𝔉` would be a new kind of amenable group.
  Being outside `LH𝔉` is not an obstruction to existence: Thompson's `F` is
  torsion-free, of type `F_∞`, and outside `LH𝔉`. It does fence off proofs of
  `F_∞` through Brown's criterion on a finite-dimensional contractible complex
  with stabilizers in `H𝔉`; the proof for `F` uses infinite-dimensional
  complexes.
