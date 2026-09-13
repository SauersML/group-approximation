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
  premise; the Bernoulli version is outside every known criterion.**
  - **Shell version.** For any bijection `nu : Gamma~ -> N`, the shell envelope
    `E_nu = <V, hat(Gamma~)>` of `shell-cantor-embeddings-are-finite-germ-extensions`
    is a finite germ extension of `V` containing a faithful copy of `Gamma~`, and
    it is a full Cantor group (`shell-envelopes-are-full-cantor-groups`). On a
    point `0^n*1*z` with `n` even, `hat(Gamma~)` moves the cone index by the left
    regular action, so that orbit's Schreier graph is a Cayley graph of `Gamma~`
    and the orbits are non-amenable. So this is exactly the host shape of the
    earlier untested item. Finite presentation of some `E_nu` settles the case
    through `fp-full-binary-cantor-groups-have-type-a-actions`. It is the instance
    `P = Gamma~` of the OPEN `decidable-inputs-have-fp-shell-envelopes`, and of the
    three clauses of `decidable-inputs-have-fp-shell-stabilizers`.
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
  - **Bernoulli version.** By
    `infinite-support-coordinate-permutations-are-nowhere-v-germs`, every
    nontrivial element of the Bernoulli action of `Gamma~` on `{0,1}^(Gamma~)` is
    singular at every point. So `<V, beta(Gamma~)>` is not a finite germ
    extension of `V`, and no known finite-presentation criterion applies to it.
  - **Specific inputs.** Property (T) and the infinite center of `Gamma~` enter
    none of the shell clauses in any known way. No clause was decided for
    `P = Gamma~`.
- **Not yet tested:**
  - Brin--Thompson groups `nV` with `n >= 2`, where the FW argument for cone
    structures does not transfer;
  - twisted Brin--Thompson envelopes over a finitely presented type (A) actor
    in which `ker p` has infinitely many conjugates;
  - vertex groups that are not residually finite in the eventually similar setting.
