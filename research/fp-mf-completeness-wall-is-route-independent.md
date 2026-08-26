---
rg: 2
id: fp-mf-completeness-wall-is-route-independent
kind: claim
title: All three Higman engines reduce finite-presentation MF-completeness to the same MF-permanence wall
distinct_from:
  machine-free-digit-reading-group-is-mf: that is the single analytic statement; this is the meta-fact that every known compiler produces an instance of it, so the wall is intrinsic to the problem rather than to one construction.
  mf-recognition-finite-presentations-is-pi2-complete: that is the target; this explains why the target is exactly as hard as one MF-permanence theorem and no easier.
---

ESTABLISHED (as a comparison of the three standard proofs of the Higman
embedding theorem).  Each proof gives a uniform `e -> T_*(P_e)` with `E`
embedded on `FIN` (hence non-MF) and a torsion-free / trivial-input output
on `INF`.  In every case the `INF`-branch output is finitely presented but
its MF-ness is unproved, and the missing step is the same:

1. **Rotman / Turing-machine (Aanderaa 1973, Rotman Ch. 12).**  Output built
   from the Boone--Britton group `G_nb(T)`.  MF-ness reduces to
   [[boone-base-has-corona-inner-instruction-automorphisms]]: a corona-inner
   family of instruction automorphisms of `(*_<x> BS(1,2)) * F(Q,q)`.  The
   obstruction is the state-letter transvection edge, a basis-to-basis free
   edge.

2. **Aanderaa--Cohen / modular machine (Cohen 1989, Simpson 2005).**  Engine
   `K_M` is MF ([[modular-machine-boone-group-is-mf]]); the compiler reduces
   to [[machine-free-digit-reading-group-is-mf]].  The obstruction is the
   digit-reading edge, a basis-to-basis free edge, incompatible with finite
   quotients by periodicity.

3. **Chiodo torsion-order-preserving (arXiv:1107.1489, Thm 2.2).**  Output
   `T(P_e)` is torsion-free on `INF`; its MF-ness is unproved.  Because
   `T(P)` is Rotman's construction with torsion tracked, its `INF`-branch
   MF-ness is literally clause 1.

**Conclusion.**  `mf-recognition-finite-presentations-is-pi2-complete` is
equivalent, over the established recursive-presentation completeness and the
established engines, to a single MF-permanence statement for a
basis-to-basis HNN edge between free subgroups of an MF group; every known
proof of Higman embedding meets this same edge.  This is the MF analogue of
the open residually-finite Higman embedding problem (Kharlampovich--
Myasnikov--Sapir 2017, Bull. Math. Sci.), and it is here isolated to the one
group `Gamma^K` of [[machine-free-digit-reading-group-is-mf]].

The route-independence is itself the reason no bookkeeping shortcut exists:
the three engines share no vertex groups except free groups and the MF
machine, and they still converge on the same free-edge permanence question.

## Proof of the reduction in each case

*(1)* [[boone-instruction-twists-extend-to-base-automorphisms]] and
[[boone-base-semidirect-product-is-hnn-over-free-subgroups]].
*(2)* [[product-commuting-aanderaa-cohen-compiler]] and
[[c-free-aanderaa-rope-is-mf-with-fine-quotients]].
*(3)* Chiodo's `T` is Rotman's Higman embedding with `Tord` tracked
(arXiv:1107.1489, discussion after Thm 2.2, citing Rotman Thm 12.18); on the
trivial-input branch it is the identity-collapse of the same rope, whose
`INF` output is the group of clause 1.

## Scope correction (2026-08-26 audit)

The equivalence claim above quantified over the three MACHINE-BASED Higman
engines, and for those the reduction to the free-edge wall stands.  But the
"and no easier" reading is refuted: the Mikhailova/graph-witness compiler
([[mf-safe-finite-presentation-compiler-via-mikhailova]]) is a fourth
route that never meets the wall, because its benign ambient is a direct
product of free groups (residually finite on every branch — the Higman
host is consulted only for its presentation, never for an approximation
property) and its final twist lands in the residually finite bridge value,
where a corona conjugator exists outright
([[twisted-hnn-mf-permanence-with-corona-conjugator]]).  Consequently
[[mf-recognition-finite-presentations-is-pi2-complete]] is closed while
[[machine-free-digit-reading-group-is-mf]] remains open as a standalone
question about `Gamma^K`; the wall is sufficient-side only, not equivalent
to the completeness target.  Independent verification of the closing chain:
`research/artifacts/mf-fp-pi2-unconditional-assembly-2026-08-26.md`.
