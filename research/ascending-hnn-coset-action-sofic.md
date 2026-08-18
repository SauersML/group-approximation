---
rg: 2
id: ascending-hnn-coset-action-sofic
kind: claim
title: The coset action of an ascending HNN skeleton is sofic when the fiber is
distinct_from:
  coordinate-action-not-sofic: That claim is a NEGATIVE soficity statement about a specific coordinate action; this is the positive open question for the lean ascending-HNN coset action, whose amenability is classical (Monod--Popa).
  marked-quotients-not-lef: That claim is a negative LEF statement about marked quotients; this is a positive soficity question about the coset ACTION of the lean HNN skeleton, feeding the sofic-plus-non-MF headline.
artifacts:
  - research/artifacts/unified-mf-compression-external-2026-08-15.md
---

OPEN.  Let Gamma be residually finite (or just sofic) and G =
<Gamma, t> the ascending HNN extension along a proper self-embedding.
Two layers:

- The GROUP G is sofic unconditionally from sofic Gamma: N = the
  directed union of t^{-n} Gamma t^n is a directed union of copies of
  Gamma (soficity passes to directed unions), and G = N x| Z is
  sofic-by-amenable (Elek--Szabo).  No open input here.
- The ACTION G on G/Gamma: amenable with explicit Folner sets by
  Monod--Popa (arXiv math/0301348, Prop 2; C. R. Acad. Sci. Canada 25
  (2003) 82-87 — same paper whose co-amenability counterexample lives
  in exactly this skeleton family).  Question: is the action sofic in
  the near-action sense consumed by the repo's
  `isSofic_iff_admitsEssentiallyFreeNearAction` framework?  If yes
  with Gamma residually finite, the finite-order-lamp wreath over
  G/Gamma is sofic AND non-MF (by [[multi-mover-collapse-criterion]]),
  giving the sofic non-MF headline through the simplest possible
  skeleton, with G far from (T) (it surjects onto Z) — a clean
  contrast to the Kun--Thom examples.

Candidate route: lane-5 telescope-window machinery transplanted —
finite-index windows in each t^{-n} Gamma t^n give finite quotient
actions of HNN truncations; Monod--Popa's Folner structure patches
the windows equivariantly.  Should be EASIER than the E-soficity lane
(no Clifford kernel to carry).  Raised by Fournier-Facio.

## Attempts

For OUR literal family the group-level statement is now closed without
any action-soficity input: [[sign-free-quotient-sofic]] proves the
sign-free quotient W/<zeta> sofic by the telescope-window pipeline, so
the sofic-and-non-MF headline does not wait on this card.  This card
remains open for the LEAN skeleton (no lamps in the group, soficity of
the coset action itself in the Gao--Kunnawalkam Elayavalli--Patchell
sense); the lane-5 window route above is the recorded attack.

Narrowed 2026-08-16.  Two flanking cases are now closed, so what is left
here is exactly the gap between them.  Finite-index image is settled by
the finite-orbit telescope ([[finite-telescope-level-coset-orbits]]).
An arbitrary self-embedding is settled whenever the base is universally
action-sofic ([[uas-base-gives-sofic-hnn-coset-action]]), which covers
LERF and the strictly larger LERA class.  The open residue is therefore
sharply stated: does residual finiteness — or soficity — of the base
imply that this one action is sofic, for an infinite-index
self-embedding?  Nothing here suggests it does; residual finiteness is
not known to imply UAS, and co-amenability of the stabilizer supplies
Folner sets in the orbit space, not the injective orbit charts the
definition wants.  Those are different data, which is why the finite-index
proof is a separate argument rather than a restatement of co-amenability.

Sharpened 2026-08-16.  Both existing sufficient conditions over-assume, and the
hypothesis can be cut down to a single subgroup.  `Cosets` is by definition
`Vertical ⧸ (iotaVertical α hα).range`, so the transitive criterion
`isSoficAction_quotient_of_separable` applies to it directly: the action is
sofic as soon as **the base copy of Gamma is a separable subgroup of G**.  UAS
constrains every action of the base and the LERF route constrains every
finitely generated subgroup of the base; the action has one point stabiliser,
so only that subgroup can matter.  Machine-checked as
`MarkedCompression.isSoficAction_vertical_cosets_of_separable_base`
(`Sofic/AscendingHNNSeparableCosetAction.lean`), with the wreath corollary
beside it.  This does not answer the question; it relocates it from soficity to
classical subgroup separability for one explicit subgroup.

What that separability unwinds to, which is the useful part.  Let
N = ker(G -> Z) = union of the levels Gamma_{-n} = t^{-n} Gamma t^n, let L be
of finite index in G with Gamma <= L, and set M = L cap N, of finite index m in
N.  Conjugating level n back to the base, M_n := t^n (M cap Gamma_{-n}) t^{-n}
is a subgroup of Gamma of index at most m, and the levels fit together as
M_n = alpha^{-1}(M_{n+1}), equivalently alpha(M_n) <= M_{n+1}, with M_0 = Gamma.
For gamma' = t^{-1} gamma t in Gamma_{-1} \ Gamma -- that is, gamma in
Gamma \ alpha(Gamma) -- one has gamma' in M iff gamma in M_1, so excluding
gamma' from L is exactly: a finite-index M_1 <= Gamma with alpha(Gamma) <= M_1
and gamma not in M_1.  That is separability of alpha(Gamma) in Gamma.  A
general gamma' in Gamma_{-k} needs the whole tower: finite-index M_k of
uniformly bounded index with alpha(M_{k-1}) <= M_k and alpha^{k-1}(gamma) not
in M_k.  The shortcut M_k = Gamma for large k is not available: then M swallows
the level containing gamma'.

This says why the two flanks behave as they do.  Over a LERF base the tower is
free, since every M_k may be taken finitely generated and separability is then
automatic -- which is the content of the UAS route, now visibly an overkill
route.  Residual finiteness separates elements from the identity, whereas the
tower asks to separate elements from the infinite-index subgroups
alpha^k(Gamma); the two are not comparable, and nothing here suggests RF
suffices.  A counterexample would be a residually finite Gamma with an
infinite-index self-embedding for which alpha(Gamma) is not separable -- easy
to arrange in isolation -- together with a proof that non-separability really
obstructs the action models rather than merely this route to them.  That
converse is the remaining gap: separability is proved sufficient, not necessary.

## Why this sits off the root graph

Nothing in the graph requires this card any more, and that is a result rather
than neglect.  The sofic-and-non-MF headline used to wait on action soficity
for this skeleton; [[sign-free-quotient-sofic]] closed it for the literal
family by the telescope-window pipeline, with no action-soficity input at all.
What is left here is the question for the LEAN skeleton — no lamps in the
group, soficity of the coset action itself — which is a cleaner statement than
the one the program needed and is nobody's prerequisite.  It is kept because
the question was raised by Fournier-Facio against a specific mechanism, and a
question with a named mechanism is worth more than the absence of a node.
