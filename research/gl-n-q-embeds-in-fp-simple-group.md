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
