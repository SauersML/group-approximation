---
rg: 2
id: steinberg-elementary-groups-are-simple-mod-centre
kind: claim
title: EL_n over the Steinberg algebra of any minimal effective ample groupoid is simple modulo its centre
distinct_from:
  free-minimal-subshift-elementary-groups-are-simple-kazhdan: that is the free minimal Z^d-subshift case, proved with box towers and adding linear soficity; this is simplicity modulo centre for every minimal effective ample groupoid, with no towers.
  minimal-subshift-algebra-is-simple-lef-ring: that is ring simplicity and LEF for d = 1; this is group simplicity of EL_n over every simple Steinberg algebra.
  binary-leavitt-elementary-group-is-simple: that is L_(F_2)(1,2) via division and Leavitt families; this covers every minimal effective ample groupoid over every field.
artifacts:
  - research/artifacts/un-steinberg-elementary-simplicity-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `k` be a field and `𝒢` a Hausdorff ample groupoid with compact infinite unit space
that is effective and minimal. Put `R = A_k(𝒢)` and `n ≥ 3`. Then:
- every normal subgroup of `EL_n(R)` is central or all of `EL_n(R)`, and `Z(EL_n(R)) ⊆ k^× I_n`;
- `S_n = EL_n(R)/Z(EL_n(R))` is an infinite simple group;
- if `k` is finite and `R` is finitely generated as a ring, `S_n` is an infinite finitely generated simple group with
  property (T).

**The two calibrating cases are both instances.**
- `LC(X, F_q) ⋊ Z = A_(F_q)(Z ⋉ X)`: the Pestov 9.1 witness.
- `L_k(1,d) = A_k(𝒢_d)`, with `𝒢_d` the Cuntz groupoid: the non-MF Leavitt units.

The non-MF tex proves simplicity of `L_(F_2)(1,2)^×` through Preusser's sandwich theorem for exchange rings; this
route needs no exchange property. So one simplicity theorem serves both constructions. Their approximation behaviour
(LEF versus no MF quotient) is decided by other invariants of the groupoid, not by simplicity.

**Credit (un-stepanov-credit, 2026-09-13).** The transvection extraction inside the ring criterion is Stepanov's Lemma
4.3 (J. Math. Sci. 95 (1999) p. 2151; `stepanov-linear-dependence-standard-normal-structure`). What is new here is the
groupoid input, local annihilation, and the uniform statement it gives. Neither Stepanov's Theorem 4.4 condition (b)
nor Vaserstein's stable-range criteria are known to hold for these algebras. See
`research/artifacts/un-stepanov-credit-2026-09-13.md`.

**Review (un-verify, 2026-09-13): PASS.** All five requires are present and established; the Lean criterion has exactly the cited hypotheses; the (T) clause is gated on finite `k` and finitely generated `R`, as EJZ needs. Subsumption scan and display check clean. See `research/artifacts/un-review-2026-09-13-part1.md` §§4–6.

**Review (sk-verify-3, 2026-09-13): PASS, second independent concurrence.** Local annihilation, the centre and the assembly re-derived; the Lean `LocalAnnihilation` definition and theorem signature checked at source (`SimpleModCentre.lean` l.43–45, l.327–329). The column-extraction case `w_l = 0` rests on the kernel check. See `research/artifacts/sk-review-3-2026-09-13-part1.md` §1.
