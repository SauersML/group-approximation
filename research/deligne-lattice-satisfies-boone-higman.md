---
rg: 2
id: deligne-lattice-satisfies-boone-higman
kind: claim
title: Deligne's non-residually-finite lattice in the universal cover of Sp_4(R) embeds in a finitely presented simple group
distinct_from:
  boone-higman-conjecture: that is the conjecture for every finitely generated group with solvable word problem; this is its test case at Deligne's lattice, a finitely presented Kazhdan group with infinite center that is not residually finite.
  higman-group-satisfies-boone-higman: that is the open case of Higman's four-generator group, which has no finite quotients and no property (T); this is the open case of a non-residually-finite Kazhdan lattice.
  deligne-lattice-embeds-in-no-rover-nekrashevych-group: that rules out every Rover--Nekrashevych host; this is the open embedding question itself.
---

**OPEN.** Let `Gamma~` be the preimage of `Sp_4(Z)` in the universal cover of
`Sp_4(R)` (`deligne-universal-cover-lattice-is-non-rf-kazhdan` with `n = 2`; any
`n >= 2` behaves the same). The question is whether some finitely presented
simple group contains `Gamma~`.

**Known inputs.**
- `Gamma~` is finitely presented, has solvable word problem, has property (T),
  has infinite center, and is not residually finite
  (`deligne-universal-cover-lattice-is-non-rf-kazhdan`,
  `deligne-lattice-embeds-in-no-rover-nekrashevych-group`, item 1).
- **Not listed.** `Gamma~` is not among the classes of BBMZ arXiv:2306.16356v3,
  Problem 5.3 (items (1)--(13) read from the extracted text on MSI,
  `bh-reviewer/2306.16356.txt`, l.886--905), and Remark 5.4 there does not
  mention it. Item (12) covers only residually finite groups. No source found
  settles the case; the search was the BBMZ text plus the repository.

## Attempts

- **Residually finite, linear and self-similar hosts: dead.** `Gamma~` is not
  residually finite; every finitely generated linear group is residually
  finite, and so is every group acting faithfully on a locally finite rooted tree
  (`self-similar-hosts-contain-only-residually-finite-groups`).
- **Rover--Nekrashevych hosts: dead.** By
  `deligne-lattice-embeds-in-no-rover-nekrashevych-group`, `Gamma~` embeds in no
  `V_d(H)` or `V_(d,r)(H)` for any self-similar `H <= Aut(T_d)`, including
  `H = Aut(T_d)`, whose Rover--Nekrashevych group is the almost-automorphism
  group.
- **Amenable-orbit full groups: dead.** By Consequence 3 of
  `kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`, every Kazhdan subgroup
  of `[[Lambda ~ X]]`, for a continuous essentially free action of a countable
  amenable group on a compact space with a full-support invariant measure, is
  residually finite.
- **Eventually similar hosts over shifts of finite type with residually finite
  vertex groups: dead.** By
  `fw-subgroups-of-eventually-similar-groups-virtually-embed`, a finite-index
  subgroup of `Gamma~` would embed in a finite product of vertex groups, forcing
  residual finiteness. Hosts whose vertex groups are not residually finite are
  not covered.
- **`Gamma~` as its own type (A) actor: dead.** By
  `type-a-actors-have-no-infinite-virtually-central-subgroup`, a group with
  infinite center has no type (A) action. Any type (A) actor containing `Gamma~`
  must give the central generator infinitely many conjugates.
- **Full Cantor hosts with non-amenable orbits (2026-09-13): reduced to the shell
  premise; Bernoulli germs give no finite germ extension of `V`.**
  - **Shell version.** For any bijection `nu : Gamma~ -> N`, the shell envelope
    `E_nu = <V, hat(Gamma~)>` of `shell-cantor-embeddings-are-finite-germ-extensions`
    is a finite germ extension of `V` containing a faithful copy of `Gamma~`, and
    it is a full Cantor group (`shell-envelopes-are-full-cantor-groups`). On a
    point `0^n*1*z` with `n` even, `hat(Gamma~)` moves the cone index by the left
    regular action, so that orbit's Schreier graph is a Cayley graph of `Gamma~`
    and the orbits are non-amenable. So this is exactly the host shape of the
    earlier untested item. Finite presentation of some `E_nu` settles the case
    through `fp-full-binary-cantor-groups-have-type-a-actions`. That is the instance
    `P = Gamma~` of the OPEN `decidable-inputs-have-fp-shell-envelopes`. The three
    clauses of `decidable-inputs-have-fp-shell-stabilizers` at `P = Gamma~` would
    suffice, through the route `three-shell-stabilizers-present-shell-envelope`.
    Belk–Hyde–Matucci Corollary 2.10 cannot certify it, since `Gamma~` is not
    virtually cyclic (`shell-isotropy-germs-fail-bhm-germ-hypothesis`). Only their
    Theorem 2.1 remains, which needs finite presentation of the `SingFix` groups.
  - **The central obstruction does not fire (hand remark).**
    `type-a-actors-have-no-infinite-virtually-central-subgroup` needs the
    centralizer of the central generator `z` to have finite index. In `E_nu` it
    has infinite index. `hat(z)` acts on even cone indices by left translation by
    `z`, which has no finite orbits because `z` has infinite order. For distinct
    even `n`, `m`, take nontrivial `v_n`, `v_m` in `V` supported in the cones
    `0^n*1*C` and `0^m*1*C`. If `v_n^(-1) v_m` commuted with `hat(z)`, then
    `hat(z)` would permute the two cones `{n, m}`, so `z^2` would fix `n` under
    left translation, which is impossible. So the cosets `v_n C_E(z)` are pairwise
    distinct.
  - **Bernoulli version.** Let `beta` be the Bernoulli action of `Gamma~` on
    `{0,1}^(Gamma~)`, identified with `C` by any homeomorphism.
    - **Not virtually cyclic.** The quotient of `Gamma~` by the infinite central
      subgroup `ker p` is the infinite group `Sp_4(Z)`. A virtually cyclic group
      has only finite quotients by infinite normal subgroups.
    - **Singular points.** By
      `conjugate-bernoulli-elements-have-uncountable-v-singular-sets`, every
      nontrivial element of `beta(Gamma~)` has uncountably many V-singular points.
      When the identification relabels coordinates,
      `infinite-support-coordinate-permutations-are-nowhere-v-germs` shows that
      every point is singular.
    - **Consequence.** No group containing `V` and `beta(Gamma~)` is a finite germ
      extension of `V`. So Belk–Hyde–Matucci Theorem 2.1, with base `V`, says
      nothing about finite presentation of `<V, beta(Gamma~)>`.
    - **Not covered.** Free actions, such as free subshifts of `Gamma~`, have
      empty fixed sets.
  - **Specific inputs.** Property (T) and the infinite center of `Gamma~` enter
    none of the shell clauses in any known way. No clause was decided for
    `P = Gamma~`.
- **SingFix clauses at `P = Gamma~` (2026-09-13, lane `solve-deligne-shell-singfix`):
  undecided. Nothing specific to `Gamma~` enters them, and the terminated-digit
  overgroup is closed.**
  - **The clauses.**
    - Belk--Hyde--Matucci Theorem 2.1 at `n = 2` is quoted verbatim in
      `research/artifacts/shell-envelope-local-tests-2026-09-13.md`. It makes
      `E_nu` finitely presented once `A_1`, `A_12` and `A_2` are.
    - `A_1` is an extension of the simple, not finitely generated neighborhood
      kernel by `Q = <rho(Gamma~), tau>`. `Q` contains the fiber product
      `R_nu x_Z R_nu` with index two (`shell-germ-group-has-index-two-fiber-product`).
    - Finite presentation of `A_1` forces `R_nu` to be an ascending HNN extension
      over a finitely generated base (`shell-germ-fp-is-an-ascending-hnn-gate`).
    - These groups see `Gamma~` only through its regular action near infinity.
      No use of property (T), the infinite center or the failure of residual
      finiteness was found in any of them.
  - **Free-near-shift obstruction: avoidable computably.**
    `central-cyclic-inputs-have-computable-mixed-near-relations` makes the
    central generator `z` act by a residue-affine permutation. That kills a
    reduced word of `Gamma~ * <s>` in `R_nu`.
  - **Fixed-base terminated-digit overgroups: dead.** By
    `fixed-base-shell-inputs-embed-in-odometer-rn-groups`, a fixed-base shell
    action would embed `Gamma~` in `V_(h,r)(<a>)`, whose Kazhdan subgroups are
    finite. So `fixed-base-shells-embed-in-contracting-rsg` never applies to
    `Gamma~`, or to any input with an infinite Kazhdan subgroup.
  - **Contracting rational similarity hosts sit at Gromov's question.**
    - Every hyperbolic group embeds in a contracting rational similarity group
      (`hyperbolic-groups-embed-in-contracting-rsgs`).
    - A theorem that Kazhdan subgroups of contracting rational similarity groups
      are residually finite would therefore make every hyperbolic group with
      property (T) residually finite. That would be the direct analogue of
      `kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf`.
    - So excluding `Gamma~` from these hosts along the lines of the
      Rover--Nekrashevych argument needs a result of that strength.
  - **Still open for `Gamma~`:**
    - residue-affine enumerations whose slopes involve several primes. Their
      markings form a product of trees, and the Kazhdan marking argument does not
      transfer;
    - finite presentation of any `S(M,M')`, or of `E_nu` itself.
- **Every finite germ extension of `V` (2026-09-18, lane `bh-kazhdan-inputs`):
  constraints on the center and on the germ regime, no exclusion.**
  - *The center is singular.* By
    `kazhdan-subgroups-of-almost-v-have-no-central-v-elements`, no nontrivial
    element of `ker p` lies in any `H`-conjugate of `V`. The proof descends the
    action to the orbit space of an attracting basin, where it runs through `V`
    and then through translation numbers.
  - *One germ group.* By `deligne-lattice-in-almost-v-sits-in-one-germ-group`, a
    finite-index subgroup of `Gamma~`, center included, embeds in a single
    singular germ group, which is finitely presented when Theorem 2.1 certifies
    the host. This kills the central kernel that the trivial-centre argument of
    `almost-v-fw-subgroups-act-through-finitely-many-germs` could not handle.
  - *The Corollary 2.10 regime is dead.* By
    `normal-germ-extensions-of-v-have-only-finite-kazhdan-subgroups`, if every
    singular germ group is virtually the `V`-germ group, or normalizes the
    `V`-dilation at a periodic point, then every Kazhdan subgroup is finite. So
    `Gamma~` needs a singular germ group that is aperiodic with infinite germs, or
    whose germs do not normalize the local dilation. Shell envelopes are of the
    second kind, and their finite presentation stays open.
- **Odometer lift over the Lagrangian Grassmannian (2026-09-18, lane `bh-free-14`):
  the lift half is done; a finitely presented host is open.**
  - *The lift.* By `deligne-extension-dies-on-lagrangian-cantor-covers`, Deligne's class
    dies on every faithful Cantor `Sp_{2n}(Z)`-space `Y` with an equivariant map to
    `Λ_n(R)`. So `Gamma~` acts faithfully on `Z_2 × Y` by
    `(x, y) ↦ (x + k(γ̃, y), γy)`, and the centre acts by `x ↦ x + 2`. It lies in the
    full group of `O_τ × (Γ ⋉ Y)`. For `Γ ≤ V` this is the mechanism of
    `odometer-lift-central-extensions-of-v-subgroups-into-2v-tau`. `Sp_{2n}(Z)` is not
    in `V`, so the base must be a higher-rank space. The natural candidate is a
    "Lagrangian Thompson group" of piecewise-`Sp_{2n}(Z)` maps on `Λ_n(R)` Cantorized
    along rational Maslov cycles. Its finite presentation is open, of the same kind
    as survey Remark 5.5.
  - *Necessary condition.* By
    `groupoid-lifts-of-central-extensions-need-no-invariant-measure`, no lift of this
    form exists over a compact `Γ`-space with an invariant probability measure. That
    covers every equicontinuous model, and so every self-similar or profinite one,
    because the class is nonzero in `H^2(Γ; R)`.
  - *Circles are excluded.* Higher-rank lattices act on `S^1` with finite image, so
    no one-dimensional model of `T̄` type exists.
- **Steinberg hosts over Leavitt rings by base change (2026-09-18, lane `bh-free-09`):
  dead.**
  - *Identification.* For `g >= 4`, `Gamma~_g ≅ StSp_2g(Z)` is the universal central
    extension of `Sp_2g(Z)`, with centre `H_2(Sp_2g(Z)) = Z`. This combines Funar--Pitsch
    and Lavrenov at source, as recorded in
    `deligne-lattice-is-universal-central-extension-for-g-ge-4`. So the lattice lifts
    injectively to `S~` whenever `Sp_2g(Z) -> S` is injective on `H_2`.
  - *Swindle.* By `leavitt-swindle-kills-deligne-center-in-ring-induced-hosts`, base
    change from `Z` into any ring with an involution-compatible Leavitt pair, `R_L`
    included, is zero on `H_2(Sp_2g(Z))` in rank `>= 6g`. So every lift to a central
    extension kills the centre.
    - Linear base change kills `2Z` for every ring, and all of `Z` once there is a
      Leavitt pair.
    - So `StSp_2g(Z) -> StSp(R_L)` does not put the lattice on the GL_n(Q) instance
      `steinberg-resolvent-shell-envelope-is-finitely-presented`.
    - A Steinberg host over a Leavitt ring must carry the centre as a genuine unit, as in
      the generic algebra-host gates.
- **Not yet tested:**
  - Brin--Thompson groups `nV` with `n >= 2`, where the FW argument for cone
    structures does not transfer;
  - twisted Brin--Thompson envelopes over a finitely presented type (A) actor
    in which `ker p` has infinitely many conjugates;
  - vertex groups that are not residually finite in the eventually similar setting.
