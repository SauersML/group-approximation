---
rg: 2
id: f-overgroups-with-a-non-integral-rational-piece-are-nonamenable
kind: claim
title: A null-set-preserving group of line homeomorphisms that contains Thurston's F and has one element agreeing on some open interval with a Moebius map in PGL_2^+(Q) outside PSL_2(Z) is nonamenable and contains no subgroup of F co-amenably; so F is the only amenable candidate among rational-breakpoint piecewise-PGL_2(Q) overgroups, and every surviving host has F's orbit relation exactly
distinct_from:
  thompson-f-co-amenable-hosts-have-integral-end-germs: that needs the non-integral germ at an end of the line, where the translation a drags every point into it, and records that for interior pieces "the method stalls there"; this removes the stall for every rational interior piece by a congruence-subgroup drag, so it covers the Lodha-Moore group G_0 (piece 2t/(1+t) on [0,1], identity near both ends) uniformly, and it adds the exact description of the survivors.
  thompson-f-is-not-co-amenable-in-its-known-nonamenable-hosts: that kills four named hosts by explicit words; this kills every overgroup of F with a non-integral rational piece anywhere.
  lodha-moore-breakpoint-orbit-is-hereditarily-amenable-not-ea: that builds the calibrator G_0 on Q and lists C^1 regularity as a survivor conditional on Lodha-Moore l.136-138; this supplies that premise (also available from the end-germ node) and shows that the integrality survivor is forced, not merely consistent.
  piecewise-projective-groups-amenable-iff-breakpoint-action-ea: that is the localized EA equivalence; this is a nonamenability criterion for overgroups of F, used together with it only in the consequences.
  thompson-t-is-isomorphic-to-ppsl2z: that identifies T with piecewise PSL_2(Z) circle maps; this is about overgroups of F on the line whose pieces leave PSL_2(Z).
  psl2z-is-almost-malnormal-and-not-co-amenable-in-thompson-t: that is about PSL_2(Z) inside T; this is about groups containing F with rational non-integral pieces.
  thompson-f-interval-orbit-relation-is-hyperfinite: that is the hyperfiniteness of F's relation, used here as an input for part 4.
  pl-ea-calibrators-are-nonamenable-interval-groups: that is the PL world; this is the piecewise projective rational world.
artifacts:
  - experiments/thompson-f-overgroups-2026-09-17/commensurator_drag.py
  - research/thompson-f-co-amenable-hosts-have-integral-end-germs-proof.md
---

**ESTABLISHED** (lane proof, not reviewed) by
`f-overgroups-with-a-non-integral-rational-piece-proof`.

**Setting.** Thurston's model as in `thompson-f-co-amenable-hosts-have-integral-end-germs`
(Lodha–Moore, arXiv:1308.4250, `vN_fp.tex` l.106–122, l.132–134, l.271–272):
- `a(t) = t + 1`;
- `b(t)` is `t` on `t ≤ 0`, `t/(1−t)` on `[0,1/2]`, `3 − 1/t` on `[1/2,1]`, and `t + 1` on `t ≥ 1`;
- `F = ⟨a, b⟩`, the `C^1` piecewise-`PSL_2(Z)` homeomorphisms of `R`.

`λ` is Lebesgue measure. A *non-integral rational Möbius map* is `ℓ ∈ PGL_2^+(Q)` that is not in the
image of `PSL_2(Z)`. Written as a primitive integer matrix `L`, it has `D = det L ≥ 2`.

**Theorem.**
1. **(Interior germs suffice.)** Let `G ≤ Homeo(R)`, of any cardinality. Assume that every element
   of `G` preserves `λ`-null sets, that `F ≤ G`, and that some `g ∈ G` agrees with a non-integral
   rational Möbius map `ℓ` on a nonempty open interval `J`. Then no countable `L_0 ≤ G` with
   `λ`-hyperfinite orbit relation is co-amenable in `G`. In particular:
   - `G` is nonamenable (take `L_0 = 1`);
   - no subgroup of `F` is co-amenable in `G`.
2. **(Named hosts.)** This covers:
   - the Lodha–Moore group `G_0 = ⟨a, b, c⟩`, through the piece `c = 2t/(1+t) = (2 0; 1 1)` on `[0,1]`,
     with `D = 2`;
   - `G_{1/2} = ⟨t + 1/2, b⟩`, with `D = 4`;
   - `⟨F, g⟩` for **any** null-set-preserving homeomorphism `g` with one such piece, whatever `g`
     does elsewhere, including elements that are the identity near both ends. The end-germ node
     does not reach these.
3. **(Rational-breakpoint rigidity.)** Let `PP_Q` be the group of homeomorphisms of `R` with finitely
   many pieces, all in `PGL_2^+(Q)`, and all breakpoints rational. Then every `G` with
   `F < G ≤ PP_Q` is nonamenable, and no subgroup of `F` is co-amenable in it. Hence, if `F` is
   amenable, it is a maximal amenable subgroup of `PP_Q`.
4. **(Exact survivors, and blindness of orbit relations.)** Let `F ≤ G`, where the elements of `G`
   are homeomorphisms of `R` with finitely many pieces in `PGL_2^+(Q)` and arbitrary breakpoints.
   Suppose `G` is amenable, or some subgroup of `F` is co-amenable in `G`. Then:
   - every piece of every element of `G` lies in `PSL_2(Z)`;
   - every breakpoint is rational or a real quadratic irrational;
   - the elements of `G` whose breakpoints are all rational lie in `F`.
   For every such "integral" `G`, `R \ Q` is `G`-invariant, and `R_G = R_F` on `R \ Q`. So `R_G` is
   `λ`-hyperfinite. More generally, every group whose elements have finitely many pieces in
   `PSL_2(Z)` has `R_G ⊆ R_F` on `R \ Q`, whether or not it contains `F`. So its relation is
   `λ`-hyperfinite too.

**Class killed (part 4).** The class is *measured orbit-relation certificates for overgroups of F*.
It includes Monod's method, Carrière–Ghys, the end-germ node, part 1 above, and the transfer lemma
`co-amenable-subgroups-transfer-hyperfinite-orbit-relations`.
- *Invariant:* the `λ`-class orbit relation `R_G` on `R \ Q`.
- *Dying step:* producing a non-hyperfinite subrelation of `R_G`. On every integral `G` the relation
  is literally `R_F`. So none of these methods can ever:
  - show an integral overgroup of `F` nonamenable;
  - exclude `F` (or its subgroups) from being co-amenable in an integral overgroup.

By parts 3–4, integral overgroups with quadratic-irrational breakpoints are the only hosts in the
rational piecewise-projective world that these methods leave open.

**Consequences for the calibrator node.**
- *The `C^1` survivor dies.* `lodha-moore-breakpoint-orbit-is-hereditarily-amenable-not-ea`, item 4,
  is now unconditional: `G_{1/2}` is nonamenable by part 2. The end-germ node gives this too. So
  `G_{1/2} ↷ Q` is a `C^1` calibrator, with pieces in `PSL_2(Z[1/2])`. Every confinement proof for
  `F ↷ D` that uses only `C^1` regularity, together with the shared germ, orbit and
  hereditary-amenability data, fails on it.
- *Integrality is forced, not merely consistent.* By part 4, integrality is a necessary condition
  for amenability among rational piecewise-projective overgroups. And any calibrator for the
  integrality survivor, meaning a nonamenable integral group acting on `Q`, cannot be certified
  nonamenable by the measured method.
- *Still open.* No single known calibrator is both `C^1` and finitely presented. `G_0` is finitely
  presented but not `C^1`; for `G_{1/2}`, finite presentability is open (l.138). A confinement proof
  that uses `C^1` and finite presentability jointly is not killed.
