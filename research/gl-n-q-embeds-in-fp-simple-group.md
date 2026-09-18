---
rg: 2
id: gl-n-q-embeds-in-fp-simple-group
kind: claim
root: true
title: For every n >= 2 the group GL_n(Q) embeds in a finitely presented simple group
distinct_from:
  rational-linear-groups-satisfy-boone-higman: that is Zaremsky's theorem for the finitely generated subgroups of GL_n(Q); this is the whole countable group GL_n(Q), which is not finitely generated and lies in no finitely generated linear group.
  char-zero-linear-groups-satisfy-boone-higman: that is every finitely generated linear group in characteristic zero; this is the countable group GL_n(Q) itself.
  boone-higman-conjecture: that is the conjecture for all finitely generated groups with solvable word problem, which implies this statement (survey Corollary 3.5); this is one named countable case.
artifacts:
  - research/artifacts/bh-survey-open-cases-status-2026-09-12.md
---

**OPEN.** For every `n >= 2` there is a finitely presented simple group `S`
and an injective homomorphism `GL_n(Q) -> S`.

**Source.** Belk--Bleak--Matucci--Zaremsky, *Progress around the Boone--Higman
conjecture*, arXiv:2306.16356v3.
- Problem 5.3, item (5): "Prove the Boone--Higman conjecture for: ... (5)
  GL_n(Q)."
- p. 7, after Corollary 3.5: "it remains an open question whether GL_n(Q)
  embeds into a finitely presented simple group."
- Problem 2.7, the related question of Bridson and de la Harpe (Kourovka
  notebook, Problem 14.10): "For n >= 2, find an explicit and natural example
  of a finitely presented group that contains GL_n(Q)." The survey says this
  part of their question "remains open".

Version v3 cites Zaremsky arXiv:2405.09722 and still lists the question as
open. That paper's Theorem 1.2 covers only the finitely generated subgroups
(`rational-linear-groups-satisfy-boone-higman`).

## Known

- **n = 1.** `GL_1(Q) = Q^x` is countable abelian, so it embeds in the finitely
  presented simple group `VA` (Belk--Hyde--Matucci, survey Theorem 4.11).
- **Finitely generated subgroups.** Every one embeds in a finitely presented
  simple group (Zaremsky, arXiv:2405.09722, Theorem 1.2).
- **Conditional.** `GL_n(Q)` has solvable word problem for its standard
  enumeration, so `boone-higman-conjecture` implies this claim (survey
  Corollary 3.5 and the paragraph after it).

## Obstructions for routes

- **O1, no residually finite overgroup.** For `n >= 2` the unipotent matrices
  `[[1,q],[0,1]]`, `q in Q`, form a copy of the divisible group `(Q,+)`. A
  divisible group has no nontrivial finite quotient, so its image in any finite
  quotient of an overgroup is trivial. A residually finite group therefore
  contains no nontrivial divisible subgroup. Hence `GL_n(Q)` lies in no
  residually finite group: in no finitely generated linear group (Mal'cev), and
  in no group acting faithfully on a locally finite rooted tree, so in no
  self-similar group. Routes through Zaremsky's self-similar affine hosts,
  the polynomial S-integer hosts of
  `char-zero-linear-groups-satisfy-boone-higman`, or any residually finite
  intermediate group cannot contain `GL_n(Q)`.
- **O2, n >= 3.** `SL_3(Z) <= GL_3(Q)` embeds in neither `V` (Higman, survey
  Theorem 4.4) nor `VA` (survey Remark 4.12). So for `n >= 3`
  neither group can serve as the host. For `n = 2`, see O4.
- **O3.** `V` contains no copy of `(Q,+)` (Higman, survey Theorem 4.4), and
  `(Q,+) <= GL_n(Q)` for `n >= 2`. So `V` is no host for any `n >= 2`.
- **O4, distortion (every n >= 2).** Burillo--Felipe, arXiv:2605.09763v1, Theorem 1:
  "Let f in VA have infinite order. Then <f> is undistorted in VA", and Corollary 5:
  "VA does not contain any group with cyclic subgroups that are distorted."
  `GL_2(Q)` contains `BS(1,2) = <x -> x+1, x -> 2x> <= Aff(Z[1/2])`, where
  `t^k a t^-k = a^(2^k)` is exponentially distorted, and `U_3(Q)` contains the
  Heisenberg group with its quadratically distorted centre. So for every
  `n >= 2` neither `GL_n(Q)`, `Aff(Q)` nor `U_3(Q)` embeds in `VA` or in any
  subgroup of it (`V`, `T-bar`, Brin's `A`). Any host must have distorted
  cyclic subgroups. By contrast Kojima--Sheng, arXiv:2603.18410v3 (Prop. 4.1,
  Thm. 4.2), embed `(Q,+)` in the Brin--Thompson groups `nV` for `n >= 2`, and
  distortion there is not settled here.
- **O5, one-manifolds (n >= 3, any copy).** `gl-n-q-hosts-cannot-act-on-one-manifolds` (5a140f21e,
  Witte via Parwani): no group acting faithfully on a one-manifold with finitely many components contains
  `GL_n(Q)` for `n >= 3`, and none acting on the line or an interval contains `SL_2(Q)`.
- **O6, scaled rational lines.** `pl-quasi-similarity-groups-scale-rational-lines-by-ratio` and
  `fg-pl-quasi-similarity-groups-contain-no-gl-2-q` (c8e0b926e): in a periodic PL quasi-similarity group of the
  line an element normalizing a copy of `(Q,+)` scales it by its own similarity ratio, so no finitely generated
  such group contains `Aff(Q)`, `B_2(Q)`, `SL_n(Q)` or `GL_n(Q)`.

## Attempts

None recorded before 2026-09-17.

1. **Lifts of circle groups (T-bar style), 2026-09-17: dead for every n >= 2.**
   `lifts-add-no-unipotent-divisibility`: if `E` is Q-free-by-central-by-Q-free,
   for example the group of all lifts to `R` of a circle group without `(Q,+)`,
   or a covering lift with Q-free deck group, then `E` contains none of
   `GL_n(Q)`, `SL_n(Q)`, `PSL_n(Q)`, `Aff(Q)`, `U_3(Q)`. The unipotent `(Q,+)`
   meets the centre trivially, so the lift cannot absorb its divisibility, and
   it must already embed in the base group. Independent of O4.

2. **Gluing affine hosts along the chain `GL_n(Z[1/m!])`, 2026-09-17: the natural
   gluing is dead.** `fg-piecewise-linear-hosts-omit-natural-gl-n-q` (via
   `fg-groups-have-fg-derivative-images`): in a finitely generated group whose
   generators have finitely many linear parts, every derivative has entries in a
   finitely generated ring, which never contains `Q`. So no finitely generated
   union of the following carries the chain with its natural action, where the
   origin is fixed and the derivative is `g`:
   - Scott's `Sc(n)`;
   - Zaremsky's affine hosts on `Z_p^n`;
   - adelic V-type groups on `A_f^n ∪ {∞}` or on `⊔_p Q_p^n`.

   In any such host, divisible subgroups and `SL_n(Q)` have trivial derivative
   at every fixed point. What survives is the Belk--Hyde--Matucci shape:
   divisibility through torsion plus a central extension, acting without fixed
   points.

3. **Adelic Cantor models, and any commutative-linear pieces, 2026-09-17: dead for
   the linear copy.** `piecewise-commutative-linear-hosts-miss-linear-gl-n-q`
   (lane gq-solenoid). Its setting:
   - `L` is topologically free and linear over a commutative ring;
   - every generator agrees locally with one of finitely many elements of `L`,
     off a closed nowhere dense set.

   Every element of such a finitely generated group that agrees with some
   `l ∈ L` on an open set has `l` in the finitely generated piece group, which is
   residually finite (Mal'cev). So `GL_n(Q)` acting through `L` never fits. No
   fixed point is needed.
   - It covers the adelic models `A_f^n ∪ {∞}` and `∏_p P^n(Q_p)`, and the adelic
     prefix group on `Ẑ`: all are non-finitely-generated. See
     `research/artifacts/gq-gq-solenoid-adelic-models.md`.
   - `germ-extensions-omit-standard-gl-n-q` extends it to groups that are locally
     in such a base off a nowhere dense set, which covers finite germ extensions.

   Surviving shape: copies whose divisible elements are not globally in `L`, as in
   `Q <= T̄` and `Q <= 2V`.

4. **Non-Thompson hosts (lattice-type groups acting on CAT(0) complexes), 2026-09-17:
   dead for every n >= 2.** `proper-semisimple-cat0-groups-contain-no-gl-2-q`: a group
   acting properly by semisimple isometries on a CAT(0) space has no distorted
   cyclic subgroup, and `BS(1,2) <= GL_2(Q)`. This excludes:
   - proper cellular actions on complexes with finitely many shapes (Bridson);
   - proper actions on CAT(0) cube complexes of any dimension (Haglund);
   - so both non-Thompson families of finitely presented simple groups in the
     survey (§4.1): the Burger--Mozes groups and the Caprace--Rémy twin building
     lattices.

   The host must be dynamical, of Thompson type or of a kind not yet built. See
   `research/artifacts/gq-heretic-assumptions.md` for the three shared assumptions
   of the current routes and what survives each denial. The survivor of the
   central-root denial is the configuration of `Aff(Q)`: an element conjugate to
   its `p`-th power for every prime `p`, through commuting conjugators.

5. **BN-pair, Curtis--Tits and local Steinberg amalgams, 2026-09-17: no reduction.**
   `sl-q-local-amalgam-gluing-is-the-whole-problem` (lane gq-borel-q):
   - `SL_m(Q)` is the colimit of its subgroups `SL_I(Q)`, `|I| <= 4`;
   - so a compatible family of homomorphisms of the pieces into one group *is* a
     homomorphism of `SL_m(Q)`, and for odd `m` an embedding.

   Gluing separately built hosts of `SL_3(Q)`-sized pieces is therefore the whole
   problem. In any host every Curtis--Tits vertex angle is `π/2`, so curvature
   criteria never apply. The rank-2 parabolic amalgam already contains `GL_3(Q)`
   Levi factors, and `P_1 *_B P_2` is not `GL_3(Q)`. Embeddability is not closed
   under amalgams in general (`bh-embeddability-forces-decidable-edge-membership`).
   - What survives: `gl-n-q-root-needs-only-nontrivial-psl-maps`. `PSL_n(Q)` is
     simple (`SL_m(Q)` for odd `m`), so a nontrivial homomorphism into an
     embeddable group suffices for infinitely many `n`; open form
     `psl-n-q-maps-nontrivially-to-fp-simple-groups`.
   - Borel side: `borel-two-q-is-units-times-aff-q` (`B_2(Q) = Q^x x Aff(Q)`).

6. **VA-pattern finite germ extensions of Higman–Thompson groups, 2026-09-17: dead for every n >= 3, for every
   embedding.** `normal-germ-extensions-of-thompson-v-contain-no-sl3z` (lane gq-germ-design). By property FW,
   `SL_3(Z)` fixes a vertex of the Belk–Hyde–Matucci germ cube complex. Margulis's normal subgroup theorem then
   embeds a finite-index subgroup into a finite product of germ groups (Theorem A, no hypothesis on the germs).
   When every singular germ group contains `(V)_p` with finite index, or normalizes it at a periodic point, the
   germ groups are abelian-by-(subgroups of `V`), and Higman's nilpotent theorem finishes (Theorem B). This
   covers `VA`, bounded-automata Röver–Nekrashevych groups, and the regime of the Belk–Hyde–Matucci Corollary
   2.10. A host for `n >= 3` needs aperiodic, non-normalizing (shell-type) germs whose finite products contain
   finite-index subgroups of `SL_3(Z)`. In the VA-pattern regime the germ groups also carry no `BS(1,2)`, so
   the distortion required by O4 cannot live in them either. `n = 2` stays open outside `VA`.

7. **Adelic covering lifts with deck group `Q^n`, 2026-09-17: dead for the natural affine part.**
   `adelic-deck-lifts-exclude-affine-q-n-and-fp-bases` (lane gq-adelic), via
   `fg-groups-with-normal-q-n-have-non-fp-quotients`. Take the adelic analogue of `R -> S^1`, the covering
   `A^n -> (A/Q)^n` with deck group `Q^n`. The deck group is a normal copy of `Q^n` in any lift group, which gives
   two facts:
   - a finitely generated lift group has monodromy in some `GL_n(Z[1/m])`, so it never carries `Aff_n(Q)` with the
     deck group as translations;
   - its base is never finitely presented, so a finitely presented Thompson-type group of the solenoid has no
     finitely generated lift group.

   Together with attempt 1, which kills lifts whose deck group is `Q`-free, covering lifts supply the divisible
   unipotent part only in a finitely generated lift group over a base that is not finitely presented, and only
   through divisible subgroups that are not contained in the deck group.

8. **Permanence closures (products, extensions, wreaths, free products), 2026-09-17:
   dead for every n >= 2.** `extension-product-closures-cannot-create-sl-n-q`: the
   class of groups that receive only trivial homomorphisms from `SL_n(Q)` contains
   every Q-free and every `BS(1,4)`-free group (residually finite, solvable, `V`,
   `T`, `VA`, `T-bar`, `A`). It is closed under subgroups, extensions, arbitrary
   direct products and free products, so under every wreath product and every
   finite-index overgroup. The permanence theorems of the permutational class
   therefore never produce `GL_n(Q)` from those bases. A route must leave the
   class through a directed union, a graph of groups with nontrivial edges, or a
   Thompson-type completion (`SV_G`, `V_d(G)`, germ extensions, `nV`).

9. **Other countable fields as testbeds, 2026-09-17 (lane gq-countable-fields).** See
   `research/artifacts/gq-gq-countable-fields-transfer.md`.
   - **O1 without divisibility.** `sl-n-of-infinite-fields-lie-in-no-residually-finite-group`:
     `SL_n(K)` has no finite quotients for every infinite field `K`, so O1 holds in every characteristic.
     Characteristic `p` does not escape it.
   - **Calibration.** `gl-n-over-algebraic-extensions-of-f-p-embed-in-v`: `GL_n(F_p-bar) <= V`. So O1-type
     facts never exclude a finitely presented simple host.
   - **O4 is characteristic-zero specific.** `char-p-linear-groups-have-no-distorted-cyclic-subgroups`.
   - **O2 persists in characteristic p.** `char-p-transcendental-gl-n-avoids-v-and-va-for-n-ge-3`, through
     the Kazhdan lattice `SL_3(F_p[t])`.
   - **Function-field analogue.** `gl-n-f2t-embeds-in-fp-simple-group` (OPEN) is the analogue with the
     unipotent difficulty removed. It has a conditional route through
     `rational-function-field-embeds-in-binary-leavitt-algebra` (OPEN).
   - **Minor.** `GL_1(Q) = Q^x ≅ Z/2 × ⊕_ω Z` already lies in `V` (survey Theorem 4.3(1)–(2)).

10. **One-dimensional piecewise-projective and PL hosts and their lifts, 2026-09-17: dead for every n >= 2,
   for every embedding.** `pp-circle-and-lift-hosts-miss-gl-n-q` (lane gq-pp-psl2q), from
   `pp-circle-divisible-subgroups-act-freely`. In a circle group whose pieces lie in a group with no divisible
   abelian subgroup (every finitely generated group of piecewise `PSL_2(R)` or PL circle maps with finitely many
   breakpoints), a divisible abelian subgroup `D` has trivial germs at any common fixed point, so it acts freely.
   Then `rot` is injective on `D`, normalizers of `D` centralize it, and `D` meets `[A,A]` trivially for amenable
   `A`. The same holds for lifts to `R` through the translation number. The unipotent `(Q,+)` of `GL_n(Q)`,
   `SL_n(Q)`, `PSL_n(Q)`, `Aff(Q)`, `B_2(Q)`, `U_3(Q)` is normalized nontrivially, or lies in `[U,U]`, so none of
   these groups embeds. This covers `T`, `T-bar`, Lodha's `S`, the Lodha--Moore groups, finitely generated subgroups
   of Monod's `H(A)`, and the Stein and irrational-slope PL groups. These hosts can contain `BS(1,2)`, so O4 does
   not reach them, and `T-bar` contains `(Q,+)`, so divisibility alone is not excluded. Not covered: `RP^(n-1)` for
   `n >= 3`, infinitely many breakpoints, and Cantor-set hosts.

11. **Brin--Thompson groups `nV` and twisted Brin--Thompson registers, 2026-09-17: gated, not dead.**
   (lane gq-bt-kojima; `research/artifacts/gq-bt-kojima-mechanism.md`)
   - `rational-stepping-stones-in-nv-need-bs12-or-heisenberg`: `Aff(Q)`, `B_2(Q)`, `SL_2(Q)` and `GL_n(Q)`
     (`n >= 2`) embed in some `nV` only if `BS(1,2)` does (`bs12-embeds-in-brin-thompson-2v`, OPEN). `U_3(Q)` and
     `GL_n(Q)` (`n >= 3`) need `H_3(Z) <= nV` (OPEN), and `n >= 3` would give an infinite Kazhdan subgroup of `nV`.
     Unlike `VA`, `nV` has distorted cyclic subgroups (Callard--Salo), so O4 does not apply; `BS(1,2)` needs
     logarithmic distortion.
   - `countable-virtually-abelian-groups-embed-in-2v`: all abelian and virtually abelian pieces (`Q^n`, tori,
     finite extensions) lie in the finitely presented simple group `2V`.
   - `twisted-bt-point-fixing-actor-elements-are-divisible`: the Kojima--Sheng register works in every `SV_G`, and
     type (A) survives adding fixed points. So in a finitely presented simple `SV_G`, actor elements fixing a point
     become infinitely divisible. The register roots give rational hulls of abelian subgroups only: commutators with
     non-commuting elements are localized on the overflow slab, and a dilation coprime to the radices acts on the
     register tower by a carry-from-below transducer (heuristic).

12. **Unions of the chain `GL_n(Z[1/m!])` and tree hosts, 2026-09-17: constraints, one kill (lane
    gq-union-obstruct).** Summary in `research/artifacts/gq-gq-union-obstruct.md`.
    - `sl-n-q-lies-in-finite-residual-of-every-overgroup`: every finite-index subgroup of every overgroup
      contains `SL_n(Q)`, which is the exact form of O1. Finite-quotient certificates of the stages never pass
      to the union.
    - `divisible-elements-act-elliptically-on-trees`: in every tree action of every overgroup, the root groups
      fix a vertex or exactly one end; with residually finite vertex stabilizers they are parabolic.
    - `gl-n-q-acts-faithfully-on-p-adic-bruhat-tits-buildings`: that parabolic case occurs, faithfully, on one
      `p`-adic building. O1's tree clause is sharp (rooted trees only), and one prime carries all
      divisibility.
    - `no-q-in-tree-product-actions-with-finite-stabilizers`: kill. No `(Q,+)` in any group acting on a product
      of trees with finite vertex stabilizers.

13. **Leavitt unit groups over commutative coefficients, 2026-09-17: a natural countable simple host, but no
   finitely presented one from them.** (lane gq-leavitt-units)
   - `leavitt-unit-groups-over-every-field-are-simple-mod-scalars`: over every field `k`, `L_k(1,2)^x / k^x` is
     simple. So `Λ = L_Q(1,2)^x / Q^x` is a countable simple group containing `GL_∞(Q)`, `V` and `SL_3(Z)`.
     Route `gl-n-q-bh-via-rational-leavitt-simple-group` reduces every `n` at once to the OPEN
     `rational-leavitt-simple-group-embeds-in-fp-simple-group`.
   - `infinite-field-leavitt-units-are-not-finitely-generated`: `Λ` is not finitely generated, and in
     characteristic zero no finitely generated subring of any `L_k(1,n)` contains `Q`. So `Q` cannot enter a
     Leavitt host through commutative coefficients.
   - `q-coefficient-leavitt-tensor-unit-groups-are-fp` (OPEN, one gap: `H_2(GL_3) = 0` in characteristic zero):
     noncommutative coefficients `B ⊇ Q` give at best a finitely presented overgroup of `GL_∞(Q)`, which serves
     `gl-n-q-explicit-natural-fp-overgroup`. Its simple scalar quotient is never finitely presented, because
     `Q^x` is central and not finitely generated. The same holds for any `Q`-algebra whose elementary groups
     contain all rational scalars.
   - `leavitt-units-over-s-integers-are-finitely-presented` (OPEN): the Khanh route fails as stated over `Z[1/m]`,
     because GE via Menal–Moncasi needs a simple ring.

14. **Every almost-V host, 2026-09-17: for n >= 3 the problem moves into one germ group (lane
    gq-germ-necessary).** `gl-n-q-almost-v-hosts-need-lattice-germs`, via the general FW germ reduction
    `almost-v-fw-subgroups-act-through-finitely-many-germs`. Let `E` be any finitely generated group of Cantor
    homeomorphisms that are locally in `V` off finite sets; this covers every finite germ extension of `V`,
    with no hypothesis on the germs. If `E >= GL_n(Q)` with `n >= 3`, then one singular germ group `(E)_p`
    contains a finite-index subgroup of every `SL_3(Z[1/m])`. The inputs are Kazhdan, the normal subgroup
    theorem, trivial centre, and the finiteness of FW subgroups of `V`. So `(E)_p` is neither amenable nor
    a-T-menable, and it lies in no `nV`. This generalizes Attempt 6's Theorem A from `SL_3(Z)` to all
    S-arithmetic `SL_3(Z[1/m])`, and to all almost-V groups. The method says nothing for `n = 2`, since every
    FW subgroup of `GL_2(Q)` is finite.
