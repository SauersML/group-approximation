---
rg: 2
id: z-localized-embeds-in-fp-rf-group
kind: claim
title: For some prime l, the additive group Z_(l) embeds in a finitely presented residually finite group
distinct_from:
  rf-higman-embedding-for-decidable-groups: that refuted statement asks for finitely presented residually finite overgroups of all finitely generated residually finite groups with solvable word problem; this asks for one specific countable, not finitely generated, residually finite abelian group.
  every-fp-rf-group-embeds-in-fp-self-similar-group: that asks for self-similar overgroups of finitely presented residually finite groups; this asks whether a finitely presented residually finite group can contain Z_(l) at all.
  sl-n-z-localized-embeds-in-fg-rf-elementary-group: that establishes the finitely generated level, with the explicit hosts E_N(R̄_l); this is the finitely presented level.
---

**OPEN.** There are a prime `l`, a finitely presented residually finite group `Λ` and
an injective homomorphism `(Z_(l), +) -> Λ`. Here `Z_(l)` is the ring of rationals
with denominators prime to `l`.

**Why it matters: a common bottleneck.** Three open host hypotheses of the gq program
each imply this claim, so each is at least as hard:
- `sl-2-z-localized-has-fp-hecke-overgroup` (for `SL_2(Q)` via Ihara and Bux--Llosa
  Isenrich--Wu), by `z-localized-fp-rf-from-hecke-overgroup`;
- `aff-n-z-localized-lies-in-fp-self-similar-group` (for `GL_n(Z_(l))` via Zaremsky),
  by `z-localized-fp-rf-from-affine-self-similar-host`;
- `rational-iwahori-group-lies-in-fp-self-similar-group` (for `PSL_2(Q)` via
  Röver--Nekrashevych groups), by `z-localized-fp-rf-from-rational-iwahori-host`.

A counterexample, meaning a proof that no finitely presented residually finite group
contains `Z_(l)` for any `l`, would kill all three routes at once.

**Constraints on a witness Λ.**
- *Not linear, not metabelian.* `Λ` is not linear over any field
  (`fg-linear-groups-have-roots-at-finitely-many-primes`), and not metabelian
  (`fg-metabelian-groups-have-roots-at-finitely-many-primes`).
- *Finite quotients.* Every finite quotient of `Z_(l)` is a cyclic `l`-group, since
  a finite-index subgroup contains some `m Z_(l) = l^(v_l(m)) Z_(l)`. So in every
  finite quotient of `Λ` the image of `1 in Z_(l)` has `l`-power order, and its
  closure in the profinite completion of `Λ` is a quotient of `Z_l`.
- *Word problem.* Every finitely generated subgroup of `Λ` has solvable word problem
  (`fp-residually-finite-groups-have-solvable-word-problem`) and is effectively
  residually finite.
- *No divisibility.* `Λ` contains no `(Q,+)` (O1), so the `l`-divisibility that the
  gq routes need must come from outside `Λ`: from a tree, an HNN letter or the level
  shifts of a Röver--Nekrashevych group.

**The finitely generated level is solved.** `Z_(l) <= E_3(R̄_l)`, a finitely generated
residually finite group (`sl-n-z-localized-embeds-in-fg-rf-elementary-group`). So the
open part is finite presentation. One concrete route is
`z-localized-fp-rf-via-fp-resolvent-elementary-group`.

## Attempts

1. **Verdict, second pass (2026-09-17, lane gq-infinite-primes): still OPEN, reduced to residual finiteness of
   one explicit finitely presented group.**
   - *The finitely presented half is done.* `Z_(l)` embeds in the finitely presented Kazhdan group
     `St_N(R_l)`, `N >= 4` (`z-localized-embeds-in-fp-kazhdan-steinberg-group`, via Krstić--McCool). The claim now
     follows from `resolvent-steinberg-group-is-residually-finite` (route
     `z-localized-fp-rf-via-rf-resolvent-steinberg-group`).
   - *A necessary condition.* That needs `R_l` to be residually finite (`steinberg-rf-forces-ring-rf`,
     `resolvent-presentation-ring-is-residually-finite`), and then the kernel of `St_N(R_l) -> E_N(R_l)` to be
     detected in finite `St_N(F)`.
   - *Sub-question 1 of `rf-resolvent-elementary-group-is-fp` fails.* `R_l` does not present `R̄_l`
     (`resolvent-ring-presentation-is-not-faithful-on-r-bar`).
   - *No known obstruction applies.* Rauzy (arXiv:2002.02540v2) and Kharlampovich--Myasnikov--Sapir
     (arXiv:1204.6506) state nothing about divisible or infinitely generated abelian subgroups. The obstructions
     found for finitely generated subgroups are solvable word problem and effective residual finiteness,
     and the explicit host `G_l` of `z-localized-embeds-in-fg-rf-soluble-group` satisfies both. So an affirmative
     answer to the effective-RF form of the Kharlampovich--Myasnikov--Sapir question, left open by Rauzy,
     would give this claim. The Kharlampovich--Myasnikov--Sapir groups themselves are soluble of class 3, as is `G_l`.
2. **Third pass (2026-09-18, lane gq-infinite-primes): the ring side is closed, and the gap is K_2.**
   - `R_l` has an explicit path normal form (`resolvent-ring-has-path-normal-form`).
   - `R_l` is residually finite for every `l` (`resolvent-presentation-ring-is-residually-finite`). So
     `E_N(R_l)` is a finitely generated residually finite group containing `Z_(l)`, and it is a quotient of the
     finitely presented `St_N(R_l)`.
   - Two new routes reduce this claim to K-theory of `R_l`:
     - `z-localized-fp-rf-via-resolvent-steinberg-rf-quotient`, from
       `resolvent-steinberg-rf-residual-is-finitely-normally-generated`;
     - `z-localized-fp-rf-via-fp-resolvent-elementary-group-over-r-l`, from `resolvent-elementary-group-is-fp`.
   - The deciding computation: do the corner tame symbols from `K_2(Z_(l)) ⊇ ⊕_(q != l) F_q^×` survive in
     `St_N(R_l)`? If they do not, or only finitely many matter, the claim follows. If infinitely many
     survive independently and `K_2(N, R_l)` is central, both routes through `R_l` fail, and the ring must be
     modified.
3. **Fourth pass (2026-09-18): the K_2 gap closes negatively for R_l, and the claim stays OPEN.**
   - Lane gq-k2-q proved `resolvent-ring-corner-symbols-survive-in-k2`. `θ_* : K_2(Z_(l)) -> K_2(R_l)` is
     injective, detected on the quotient `R_l / J ≅ D ⊕ M_Z^fin(Z_(l))` by Suslin excision and Morita. So the corner
     tame symbols `{q, g_q}`, `q != l`, give an infinitely generated subgroup of stable `K_2`. Checked by this lane:
     `J` is an ideal by the multiplication rules of `resolvent-ring-has-path-normal-form`, and the quotient
     multiplies as matrix units.
   - Consequences:
     - `resolvent-elementary-groups-are-not-fp` refutes `resolvent-elementary-group-is-fp`, so route
       `z-localized-fp-rf-via-fp-resolvent-elementary-group-over-r-l` is closed.
     - `resolvent-steinberg-rf-residual-is-infinitely-normally-generated` is ESTABLISHED, with both K-theory
       inputs read at source (69ed7e51a; confirmed by gq-referee-b, 7a9be50ac). It closes route
       `z-localized-fp-rf-via-resolvent-steinberg-rf-quotient`.
     - For `l` odd the surviving corner symbols lie in the finite residual, so `St_N(R_l)` is not residually
       finite. `resolvent-steinberg-group-is-residually-finite` stays open only at `l = 2`.
   - **What is NOT refuted.**
     - This claim itself. It asks for some finitely presented residually finite group containing `Z_(l)`, and the
       obstruction concerns quotients of `St_N(R_l)` only.
     - A finitely presented residually finite quotient of `St_N(R_l)` whose kernel strictly contains the finite
       residual is not excluded; whether `Z_(l)` survives in one is unknown.
   - **Standing assets.**
     - `R_l`: a finitely presented residually finite ring with `Z_(l)` in a corner.
     - `E_N(R_l)`: finitely generated and residually finite.
     - The effectively residually finite soluble host `G_l` (`z-localized-embeds-in-fg-rf-soluble-group`).
   - **The lesson for new routes.** Any ring route must also kill `K_2` of the scalars it adds. Two devices kill
     the corner in finite quotients: divisibility of `[e]`, and Leavitt pairs. So neither helps (artifact
     `gq-gq-k2-q-resolvent-corner.md` §3). Non-Steinberg routes, such as Kharlampovich--Myasnikov--Sapir-type
     constructions for `G_l`, are untouched.
4. **Route (a), Kharlampovich--Myasnikov--Sapir groups (2026-09-18, lane gq-infinite-primes): excluded.** Read
   from the arXiv:1204.6506v5 e-print; artifact `gq-gq-infinite-primes-kms-reading.md`.
   - The paper proves no embedding theorem. Its §1.1.7 only poses the unrestricted residually finite Higman
     question.
   - Its groups `G(M)` lie in `𝒜_p^2 𝒜` (Theorem 4.3(a)), so every torsion-free subgroup is free abelian of finite
     rank (`kms-minsky-groups-contain-no-z-localized`). No `G(M)` contains `Z[1/q]`, `Z_(l)` or `G_l`.
   - The failing hypothesis is the exponent-`p` base. A characteristic-0 variant of the KMS construction, with a
     `Z_(l)`-module base over a finitely presented metabelian top, is not supplied by the paper. It would need three
     new ingredients:
     - a finitely presented metabelian extension of the `Z ≀ Z`-action;
     - finitely many module relations;
     - a residual-finiteness proof that does not use finite exponent (the paper's Theorem 4.17 does).
5. **A characteristic-0 KMS variant: calibration (2026-09-18, lane gq-infinite-primes).**
   - *Known limit of the general question.* The unrestricted residually finite Higman embedding (every finitely
     generated residually finite group with solvable word problem embeds in a finitely presented residually
     finite group) is false: E. Rauzy, *Obstruction to a Higman embedding theorem for residually finite groups
     with solvable word problem*, arXiv:2002.02540v2 (17 Mar 2021), Theorem 1
     (`rf-higman-embedding-for-decidable-groups-fails`). His counterexample is not effectively residually finite,
     while `G_l` is.
   - *The naive variant is inconsistent.* Relations G1–G8 with only the base exponent law dropped still force
     `x_(uA_i)^p = 1` (`kms-configuration-letters-inherit-exponent-p`). The exponent law on the A-letters,
     transported by G5 a), kills torsion-freeness.
   - *The fully characteristic-0 variant.* Dropping the A-letter exponent too gives what artifact
     `gq-gq-infinite-primes-kms-reading.md` §4 analyses, without proof. Residual finiteness would plausibly
     survive, with finitely generated abelian quotients of `T` in place of finite ones. But the base would be free
     abelian, so the group would contain no `Z_(l)`. The crux moves to ingredient (2): a module relation with a
     non-unit scalar, such as the Euler relation of `G_l`. With that relation, ingredient (3) is hard again.
6. **Ingredient (2) for the Euler base: the freest extension fails (2026-09-18, lane gq-infinite-primes).**
   `euler-base-annihilator-over-lamplighter-is-not-fg`:
   - Over the ring `D` the Euler base `M = Z_(l)[y^(±1)]` needs one left relation and one two-sided relation
     (the Euler element `r = xβx^(-1) - β - l`).
   - Over `Z[Z≀Z]` its annihilator is not finitely generated. So finitely many of the shifted Euler relations
     `r x^k f_0 = 0` never suffice.
   - The induced module over any overgroup `Q ⊇ Z≀Z`, Baumslag's finitely presented metabelian group
     included, is not finitely presented.
   - At the generator, the Euler relation is a BR-conjoint relation (KMS Lemma 4.1 form, pair `(β_(-1), β)`,
     polynomial `t - l`). But BR propagates along the lamps, not along `x`.
   - Open: a finitely presented base that is a proper quotient of the induced module and still contains `M`.
     Deliverable (a), an explicit finite presentation, is not achieved.
7. **A finitely presented host with no corner obstruction (2026-09-18, lane gq-infinite-primes).**
   - *The ring.* Put the Euler base in the off-diagonal corner of `T_l = [[D, D/Du],[0, Z]]`
     (`euler-triangular-ring-is-fp-rf`). `T_l` is a finitely presented residually finite ring.
   - *The group.* `St_N(T_l)` is finitely presented for `N >= 5` (rank-five node) and contains the Euler base
     `M ⊇ Z_(l)` through `x_12` (`euler-base-embeds-in-fp-steinberg-group`). `E_N(T_l)` is finitely generated,
     residually finite, and contains `G_l`.
   - *Why the corner obstruction goes away.* The Steinberg commutator relations carry the `D`-action on `M`,
     so the Euler relation needs only the finitely many relations of the ring `D`. `Z_(l)` is now a
     square-zero bimodule, not a corner ring, so the tame-symbol obstruction for `R_l` has no analogue.
   - *What remains.* Only residual finiteness:
     - `euler-triangular-steinberg-rf-residual-is-fng` suffices (route
       `z-localized-fp-rf-via-euler-triangular-steinberg`);
     - in turn it follows from `euler-triangular-ring-has-fg-central-unstable-k2`.
     - Heuristically, stable `K_2(T_l) = K_2(D) ⊕ K_2(Z)` is finite. Three inputs are unread: triangular
       K-theory, the twisted Laurent theorem, and stability.
   - This is the most promising live route to the bottleneck.
8. **The triangular route after gq-k2-q (2026-09-18, lane gq-infinite-primes).**
   - gq-k2-q (29881297a) showed that the Euler ring `D` has infinite-rank `K_2`, via the symbols
     `{π_0, π_q}`. So `K_2(N, T_l)` is not finitely generated, and neither `E_N(T_l)` nor `E_N(D)` is finitely
     presented.
   - `St_N(D)` is a retract of `St_N(T_l)` (`euler-triangular-steinberg-retracts-to-euler-steinberg`). So the
     triangular route needs `euler-ring-steinberg-rf-residual-is-fng`: whether infinitely many independent
     `{π_0, π_q}` die in every finite quotient. That question is NOT decided. The partial analysis and the
     smallest test ring are in that node's Attempts.
   - **Design constraint.** `Z_(l)` in the base comes from the lamps `π_k` acting invertibly. Finite
     presentation needs that invertibility as ring relations, which makes the `π_k` units and creates the
     symbols. This lane has no concrete way to decouple the two.
