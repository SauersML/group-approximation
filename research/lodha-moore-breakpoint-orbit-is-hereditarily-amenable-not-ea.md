---
rg: 2
id: lodha-moore-breakpoint-orbit-is-hereditarily-amenable-not-ea
kind: claim
title: The Lodha--Moore group acts on the rationals, the breakpoint orbit it shares with Thompson's F, hereditarily amenably but not extensively amenably
distinct_from:
  pl-ea-calibrators-are-nonamenable-interval-groups: that shows no piecewise linear world separates amenability from extensive amenability on breakpoints unless PL_+([0,1]) has a nonamenable subgroup; this gives a separating world one regularity class up, acting on the very set Q on which F acts, with finite presentability, no free subgroups and hereditary amenability shared with F.
  thompson-f-is-not-co-amenable-in-its-known-nonamenable-hosts: that shows F is not co-amenable in G_0 (the coset space); this is about G_0 acting on points of Q, and calibrates extensive amenability of F's own breakpoint action, not a host route.
  piecewise-projective-groups-amenable-iff-breakpoint-action-ea: that is the general localized equivalence; this is its application to G_0, F and <t+1/2, b>, together with the orbit computation B = Q and the class kill for the confinement hole.
  f-dyadic-inverted-orbit-is-subballistic-on-rare-events: that is the open confinement statement for F; this exhibits a transitive, hereditarily amenable action on the same set in which the confinement provably fails at an exponential rate.
artifacts:
  - experiments/lodha-moore-ea-calibrator-2026-09-17/orbit_of_zero.py
---

**ESTABLISHED** (lane proof, not reviewed). Proof route:
`lodha-moore-breakpoint-orbit-not-ea-proof`.

**Setting.** Thurston/Lodha–Moore maps of `R` (arXiv:1308.4250, `vN_fp.tex` l.106–122):
- `a(t) = t + 1`;
- `b(t)` is `t` for `t ≤ 0`, `t/(1−t)` on `[0, 1/2]`, `3 − 1/t` on `[1/2, 1]`, and `t + 1` for `t ≥ 1`;
- `c(t) = 2t/(1+t)` on `[0,1]`, and `t` otherwise.

Groups: `F = ⟨a, b⟩` (Thompson's group), `G_0 = ⟨a, b, c⟩` (nonamenable and finitely presented), and
`G_{1/2} = ⟨t ↦ t + 1/2, b⟩`.

**Theorem.**
1. **Breakpoint orbit.** `sing(a) = ∅`, `sing(b) = {0, 1/2, 1}` and `sing(c) = {0, 1}`. The `F`-orbit of
   `0` is all of `Q`. Hence `B(F) = B(G_0) = B(G_{1/2}) = Q`, each a single orbit, and `F`, `G_0` and
   `G_{1/2}` all act transitively on `Q`.
2. **The calibrator.** `G_0 ↷ Q` is hereditarily amenable but not extensively amenable. Equivalently,
   `(Z/2)^{(Q)} ⋊ G_0` acting affinely on `P_f(Q)` has no invariant mean. Quantitatively: let `μ` be
   symmetric, finitely supported and non-degenerate on `G_0`, let `x_0 ∈ Q`, and let `O_n` be the inverted
   orbit. Then for some `ε > 0`, `P(|O_n| < εn) ≤ e^{−εn}` for all large `n`.
3. **F on the same set.** `F ↷ Q`, the restriction of this action, is extensively amenable iff `F` is
   amenable, iff `F ↷ D` is extensively amenable, iff `f-dyadic-inverted-orbit-is-subballistic-on-rare-events`
   holds.
4. **Conditional C^1 calibrator.** Lodha–Moore assert without proof (l.136–138) that `G_{1/2}` is
   nonamenable. If so, `G_{1/2} ↷ Q` is a second calibrator of the same kind. Every element of `G_{1/2}`
   is `C^1`, and its pieces lie in `PSL_2(Z[1/2])`.

**Class killed (confinement / EA proofs for F from shared action data).** `F ↷ Q` and `G_0 ↷ Q` agree
on the following. The set is the same (`Q`), and `F ≤ G_0` acts by restriction, with the same single orbit.
- *Orbit amenability:* both are hereditarily amenable. So every Schreier graph of every subgroup, on every
  orbit, is amenable. The mechanism is the same in both: germ Følner rays towards the supremum of each
  orbit, where the double commutator of `Stab_{PSL_2(R)}(M)` dies (JMMdlS l.771–790).
- *JNS germ data:* finitely many singular points per generator, all in `Q`; isotropy germs in
  `Aff × Aff`; `[[𝓗]] = Aff(R)`; pieces in `PGL_2(Q)`; translation germs at `±∞` (`a` in both groups).
- *Group-theoretic:* finitely presented, torsion-free, no non-abelian free subgroups, and containing `F`
  together with its breakpoint orbit.

*Invariant:* the JNS inputs (1), (2), (4) hold for both, and so does hereditary amenability. Only (3′),
extensive amenability on the breakpoint orbit, can differ.

*Dying step:* the upgrade "hereditarily amenable (plus the germ data above) ⇒ extensively amenable". Any
proof of `f-dyadic-inverted-orbit-is-subballistic-on-rare-events` whose inputs are drawn only from the list
above is also a proof that `G_0 ↷ Q` is extensively amenable. That contradicts item 2, which gives
exponential failure of confinement for `G_0`.

This corrects `pl-ea-calibrators-are-nonamenable-interval-groups` on one point. That node says "no PL world
can currently test" F-specific inputs such as finite presentability. One regularity class up, the
finitely presented `G_0` tests finite presentability, the absence of free subgroups, and rational
breakpoints, and it passes all of them while failing extensive amenability.

**What survives.** A proof for `F` must use an input that `G_0` lacks:
- *Unimodular integrality:* the pieces of `F` lie in `PSL_2(Z)`, while `c` has matrix `(2 0; 1 1)` of
  determinant 2. This is consistent with `thompson-f-co-amenable-hosts-have-integral-end-germs`.
- *`C^1` regularity:* `c` has one-sided slopes `1, 2` at `0` and `1/2, 1` at `1`. This input is killed too
  if item 4's premise (Lodha–Moore l.136–138, unproved in the source) holds.
- *The specific relations of `F`.*

Not covered: whether some nonamenable subgroup of `H` with pieces in `PSL_2(Z)` exists (it would kill
integrality); whether `G_{1/2}` is nonamenable.

## Attempts

- **2026-09-17, swarm-0917-w14-w14-f-last1 (host-geometry). Item 4 is unconditional; the `C^1`
  survivor dies; integrality is forced.**
  - *Premise of item 4.* `G_{1/2}` is nonamenable. Two independent sources give this:
    - part 2 of `thompson-f-co-amenable-hosts-have-integral-end-germs`, through the end germ `t + 1/2`;
    - part 2 of `f-overgroups-with-a-non-integral-rational-piece-are-nonamenable`, through a
      congruence drag that needs only an interior piece.
    So `G_{1/2} ↷ Q` is a `C^1` calibrator with pieces in `PSL_2(Z[1/2])`. The survivor "`C^1`
    regularity" in "What survives" is killed.
  - *Integrality is forced.* Part 4 of the new node: if `F ≤ G` and `G` has finitely many
    `PGL_2^+(Q)` pieces per element, then amenability of `G` forces
    - all pieces into `PSL_2(Z)`;
    - all breakpoints into `Q` or real quadratic irrationals;
    - all rational-breakpoint elements into `F`.
  - *The integrality survivor cannot be calibrated by measured orbit relations.* The "Not covered"
    question above asks for a nonamenable subgroup `G` of `H` with pieces in `PSL_2(Z)`. Any such
    group has `R_G ⊆ R_{PSL_2(Z)} = R_F` on `R \ Q`, with equality when `F ≤ G` (part 4 of the new
    node). That relation is hyperfinite, so
    Monod- or Carrière–Ghys-type arguments cannot certify its nonamenability. The invariant is the
    measured orbit relation, and the step that dies is "exhibit a non-hyperfinite subrelation".
  - *Still standing.* Specific relations of `F`, and the joint input "`C^1` and finitely presented".
    `G_0` is not `C^1`, and finite presentability of `G_{1/2}` is open (l.138).
