# Boone--Higman for compact 3-manifold groups (lane solve-bh-3manifold, 2026-09-13)

## Verdict

Partial. Membership in `B_A` (the permutational Boone--Higman class) is proved
for every compact 3-manifold group, except when a prime summand of the
orientation cover is a closed graph manifold with non-trivial JSJ decomposition
that is not virtually fibered. The exceptional case is the open node
`nonfibered-closed-graph-manifold-groups-satisfy-pbh`. Nothing here has been
independently reviewed.

Nodes:
- `three-manifold-groups-linear-unless-closed-graph-manifold` (import) with route
  `three-manifold-groups-linearity-citation`;
- `based-dehn-nielsen-baer-for-closed-surfaces` (import) with route
  `based-dehn-nielsen-baer-citation`;
- `virtually-fibered-3-manifold-groups-satisfy-pbh` with route
  `virtually-fibered-3-manifold-pbh-proof`;
- `three-manifold-groups-pbh-off-nonfibered-graph-manifolds` with route
  `three-manifold-pbh-case-analysis-proof`;
- OPEN: `nonfibered-closed-graph-manifold-groups-satisfy-pbh`, and
  `compact-3-manifold-groups-satisfy-pbh` with route
  `compact-3-manifold-pbh-via-nonfibered-graph-case`.

## Sources and verbatim pins

All TeX sources were fetched on MSI into `/scratch.global/sauer354/bh-3manifold/`.

### Aschenbrenner--Friedl--Wilton, *3-manifold groups*, arXiv:1205.0202

File `3-manifold-groups-new-version-032613.tex`.

- l.291, conventions: "All spaces are assumed to be connected and compact and
  all groups are assumed to be finitely presented, unless it is specifically
  stated otherwise."
- l.318: "if N is an orientable prime 3-manifold with no spherical boundary
  components, then by [Hem76, Lemma 3.13] either N is irreducible or N = S1 × S2."
- l.322--331, Theorem `thm:prime`: "Let N be a compact, oriented 3-manifold with
  no spherical boundary components. [...] In particular, π1(N) = π1(N1) ∗ ··· ∗
  π1(Nr) is the free product of fundamental groups of prime 3-manifolds."
- l.1715--1718, (C.1): "Let N be an irreducible, orientable 3-manifold with
  infinite fundamental group. It follows from the irreducibility of N and the
  Sphere Theorem [...] that π2(N) = 0. Since π1(N) is infinite, it follows from
  the Hurewicz theorem that πi(N) = 0 for any i > 2, i.e., N is an
  Eilenberg–Mac Lane space."
- l.2606--2609: "we say that a 3-manifold N with empty or toroidal boundary is
  non-positively curved if the interior of N admits a complete non-positively
  curved Riemannian metric. Furthermore, a compact orientable irreducible
  3-manifold with empty or toroidal boundary is called a graph manifold if all
  JSJ components are Seifert fibered manifolds."
- l.2613--2616, Theorem `thm:leeb` (Leeb): "Let N be an irreducible 3-manifold
  with empty or toroidal boundary. If N is not a closed graph manifold, then N
  is non-positively curved."
- l.2620--2622, Theorem `thm:liu11` (Liu): "Let N be an aspherical graph
  manifold. Then π1(N) is virtually special if and only if N is non-positively
  curved."
- Remarks after `thm:liu11`: "There exist closed graph manifolds with
  non-trivial JSJ decompositions that are not virtually fibered (see, e.g.,
  [LuW93, p. 86] and [Nemb96, Theorem D]) [...] There also exist fibered graph
  manifolds which are not virtually special [...] also see [Liu11, Section 2.2]
  and [BuS05] for examples with non-trivial JSJ decomposition which are not torus
  bundles."
- l.2659--2662, Theorem `thm:npcvs`: "Let N be a compact orientable aspherical
  3-manifold N with empty or toroidal boundary. Then π1(N) is virtually special
  if and only if N is non-positively curved."
- l.2738--2743, Corollary `cor: Non-toroidal properties`: "Let N be a compact,
  orientable, aspherical 3-manifold with non-empty boundary. Then (1) π1(N) is
  linear over Z".
- l.2046: "Groups which are virtually polycyclic are linear over Z by the
  Auslander--Swan Theorem".
- l.3158--3162: "Let p: N → S1 be a fibration with surface fiber Σ. We obtain a
  short exact sequence 1 → Γ := π1(Σ) → π = π1(N) → Z = π1(S1) → 1. This sequence
  splits and we see that π is isomorphic to the semidirect product Z ⋉φ Γ".
- (G.24), l.3208: "Hsu and Wise [HsW99, Corollary 3.6] showed that any RAAG is
  linear over Z".
- (H.lineargreen), l.3268--3270: if π is linear over R and has finite index in
  π′, "It follows that π′ is also linear over R."
- Corollary `cor: HW special`: "Every special group is a subgroup of a
  right-angled Artin group."
- l.3327: "Svetlov [Sv04] proved that non-positively curved graph manifolds are
  virtually fibered."
- l.3702--3704, Theorem `thm:Seifert linear`: "Let N be a Seifert fibered
  manifold. Then π1(N) is linear over Z." (proof by Boyer, l.3708--3787)
- l.3742: "We first recall that surface groups are linear over Z."
- l.4283ff: "We now know that the fundamental groups of most 3-manifolds are
  linear." Button [But12a] gives a closed graph manifold with no faithful
  representation in GL(4, k) for any field k.

### Douba, *Virtually unipotent curves in some non-NPC graph manifolds*, arXiv:2101.06797

- Abstract: for a graph manifold with one JSJ torus and blocks `Σ × S^1` that is
  not NPC, "there is an essential curve on T such that any finite-dimensional
  linear representation of π1(M) maps an element representing that curve to a
  matrix all of whose eigenvalues are roots of 1. In particular, this shows that
  π1(M) does not admit a faithful finite-dimensional unitary representation, and
  gives a new proof that π1(M) is not linear over any field of positive
  characteristic."
- l.206: "Button [...] proved that any finitely generated group Γ satisfying
  (positivechar) acts properly by semisimple isometries on a complete CAT(0)
  metric space, and Leeb [...] showed that if the fundamental group of a graph
  manifold M admits such an action, then M is NPC. At the time of writing of this
  article, it is not known if a single non-NPC graph manifold without Sol
  geometry admits a faithful finite-dimensional linear representation over a
  field of characteristic zero."

### Farb--Margalit, *A primer on mapping class groups*

PDF fetched on MSI, text extracted locally.
- Section 1: "If S admits a hyperbolic metric, then the centralizer of any
  non-trivial element of π1(S) is cyclic. In particular, π1(S) has a trivial
  center."
- Section 8.2, "Once-punctured versus closed": "The five lemma then tells us that
  the middle vertical map is an isomorphism from Mod±(Sg,1) to Aut(π1(Sg))."

### BFFHZ, arXiv:2503.21882v2

Extracted text `/scratch.global/sauer354/bh-outfn-mcg/2503.21882v2.txt`.
- Corollary B, first bullet: "The (extended) mapping class group of an orientable
  surface Σ of finite type, where Σ either has non-empty boundary, at least one
  puncture, and/or genus at most two."
- l.180--181, Corollary F: "If A and B satisfy the permutational Boone–Higman
  conjecture, then the free product A ∗ B also satisfies the (permutational)
  Boone–Higman conjecture."
- l.667--671, Remark 4.1: "let α ∈ Aut(Fn) and consider the free-by-cyclic group
  Fn ⋊α Z. If α has infinite order in Out(Fn), then the action by conjugation on
  Fn induces an embedding Fn ⋊α Z → Aut(Fn) and we conclude by Theorem A.
  Otherwise Fn ⋊α Z is commensurable to Fn × Z".

The fibered lemma here is this argument with `Aut(π1(Σg)) = Mod±(Sg,1)`.

### BBMZ survey, arXiv:2306.16356v3

- Theorem 5.1 (7), (8): "Fundamental groups of compact 3-manifolds that admit a
  Riemannian metric of nonpositive curvature. (8) Fundamental groups of
  finite-volume hyperbolic 3-manifolds."
- Problem 5.3 lists braid groups, MCGs, Aut/Out(F_n), BS(m,n), GL_n(Q), Burnside
  groups, fp metabelian, free-by-cyclic, torsion-free one-relator, CAT(0),
  automatic, fp residually finite, and Artin groups. No 3-manifold item.

### Bux--Llosa Isenrich--Wu, arXiv:2408.05673

- l.283: "Let G be a group and let 𝒢 be a locally finite infinite graph which G
  acts on." Rigid permutation groups are defined only for such graphs (l.287,
  l.360).

## Novelty search (bounded)

- The repo;
- the survey, BFFHZ, BLIW and AFW;
- web queries: "closed graph manifold fundamental group linear open question",
  "Boone-Higman conjecture 3-manifold groups ...", "graph manifold groups linear
  faithful representation 2024-2026", and "graph manifold group embeds in mapping
  class group".

None printed the theorem. Experts may regard it as folklore, so no priority is
claimed.

## Exact gap

For a closed graph manifold `N` with non-trivial JSJ decomposition and no fibered
finite cover, put `pi_1(N)` in `B_A`. Candidate hosts are:
- a faithful characteristic-zero representation, open by Douba l.206;
- an embedding in the mapping class group of a punctured surface, untested;
- a type (A) actor realizing the `Z^2`-amalgams of the JSJ graph of groups.
