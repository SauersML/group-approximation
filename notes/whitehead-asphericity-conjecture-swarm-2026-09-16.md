# Whitehead asphericity conjecture: swarm attack, 2026-09-16

Target: `whitehead-asphericity-conjecture` (root, OPEN). Lock taken by
`swarm-whitehead-asphericity-conjectu`. Notes only: no `research/` node was
written, for the reasons in section 6.

Outcome in one paragraph.
- **Literature.** The dated literature gate finds the conjecture still open.
- **Claimed proofs.** Kawauchi's arXiv:2303.04368v2 and its finite predecessor
  arXiv:2212.02617v3 were read at source level. Their load-bearing input is
  Theorem 1.4 of arXiv:2212.02617: every ribbon disk-link exterior in `D^4` is
  aspherical. That is Howie's ribbon disc complement conjecture.
- **Section 3.** A source-level reading shows that the justifications offered
  for Theorem 1.4 (section 5.1 of that paper) never use that the singular
  surface is a sphere. A rigorous argument (Propositions A and B, with one
  recalled realization fact) shows that the torus analogue of its conclusion is
  false. So the argument is incomplete as written. This is not a counterexample
  to anything.
- **Section 4.** An elementary wedge construction turns every counterexample
  into a type-(b) chain, *as type (b) is paraphrased by Cerdeiro–Minian*. In that
  wording, "no type-(b) chain exists" is the whole conjecture. Howie's and Luft's
  original statements were not read, so no claim is made about them.

## 1. Setup

**Conjecture (Whitehead 1941).** Every connected subcomplex of an aspherical
2-complex is aspherical.

For a connected 2-complex, aspherical means `pi_2 = 0`, by Hurewicz applied to
the universal cover.

**Standard first reduction (elementary, used below).** Let `L` be aspherical
with universal cover `p : L~ -> L`, and let `K` be a subcomplex of `L`. Every
component of `p^{-1}(K)` is a covering space of `K`, so its `pi_2` is
`pi_2(K)`. `L~` is contractible. So the conjecture is equivalent to:

> every connected subcomplex of a contractible 2-complex is aspherical.

The negation of that statement is the graph's refuter claim
`nonaspherical-subcomplex-of-contractible-2-complex-exists`.

**Compactness.** An essential map `S^2 -> K` has compact image, so it lies in a
finite connected subcomplex `A_0`. It is still essential there, since a
nullhomotopy in `A_0` would be one in `K`. So a counterexample always contains
a finite non-aspherical `A_0`.

**Howie's reduction.** Pinned from the source of Cerdeiro–Minian,
arXiv:1203.5348v1, lines 107–111; already quoted in
`research/artifacts/ideas-bridges-2-2026-09-14.md` S2. If the conjecture fails,
there is a counterexample `K ⊂ L` of one of two types.

- **(a)** `L` finite and contractible, `K = L - e` for a 2-cell `e`, and `K`
  non-aspherical.
- **(b)** `L` the union of an infinite chain `K = K_0 ⊂ K_1 ⊂ ...` of finite
  non-aspherical subcomplexes, each inclusion `K_i -> K_{i+1}` nullhomotopic.

The same source, line 114: "In 1996 E. Luft [lu] proved that the existence of a
counterexample of type (a) actually implies the existence of a counterexample
of type (b)." Luft, Math. Proc. Camb. Phil. Soc. 119 (1996) 493–495, not read
(unverified beyond that bibliographic line).

**Graph neighbourhood read this session.**

- Bestvina–Brady route `nonaspherical-subcomplex-via-bestvina-brady-kernel`.
  Its open input is `bestvina-brady-poincare-kernel-has-geometric-dimension-two`.
- One-cell / L² chain.
  - `one-cell-l2-vanishing-gives-one-cell-whitehead` targets
    `contractible-2-complex-minus-a-cell-is-aspherical`.
  - Open inputs: `one-cell-complement-groups-have-vanishing-first-l2-betti` and
    `non-ascending-one-cell-complements-have-vanishing-l2-b1`.
  - Established: `whitehead-one-cell-counterexamples-have-positive-first-l2-betti`,
    `one-cell-complement-cyclic-cover-homology-is-finite`,
    `lo-amenable-limit-one-cell-complements-are-aspherical`.
- LOT side: `lot-asphericity-via-whitehead-conjecture` and
  `labeled-oriented-trees-are-aspherical` (OPEN).
- Existing Kawauchi audit: `kawauchi-weak-kervaire-rests-on-unresolved-inputs`
  with route `kawauchi-dependency-audit`.
  - It is an abstract-level audit, scoped to the Kervaire–Laudenbach import. It
    invalidates `kl-via-weak-conjecture-import`.
  - The route says explicitly that the manuscript bodies were not read and that
    arXiv:2303.04368 was not fetched.
  - Section 3 below is the body-level continuation for the Whitehead part of the
    chain.

## 2. Literature gate

Checked 2026-09-16. arXiv abstract pages were fetched with curl and their
citation meta tags read; arXiv API metadata was saved from a search on the same
day. The session's web-search quota was exhausted before this gate, so the gate
is not an exhaustive search.

**Verdict: OPEN.** No refereed resolution found. The claimed proofs are unrefereed
preprints; section 3 shows the load-bearing step is incomplete as written.

Items pinned, newest first.

1. S. P. Fisher, Y. Lodha, *A note on normal generation and the first
   ℓ²-betti number*, arXiv:2608.25988v1, submitted 26 Aug 2026.
   - The abstract lists "an important special case of the Whitehead asphericity
     conjecture" among the consequences of the Osin–Thom conjecture, and states
     "This disproves the conjecture." It adds: "However, they are not finitely
     generated."
   - Status evidence: WC is still framed as a conjecture in August 2026.
   - Graph effect: none new. The graph already carries this as
     `l2-normal-rank-bound-fails-for-torsion-free-groups`. The one-cell L²
     chain in section 1 concerns finitely presented groups, which the
     counterexamples are not.
2. J. Harlander, S. Rosebrock, *Local indicability in the presence of
   diagrammatic reducibility*, arXiv:2511.15212. v1 is dated 19 Nov 2025; the
   page reads "last revised 31 May 2026 (this version, v2)". The abstract says
   "We apply this to the question of local indicability in the context of
   Whitehead's asphericity conjecture." Status evidence: specialists still call
   it a conjecture in 2026.
3. google-deepmind/formal-conjectures issue #2189, *Whitehead asphericity
   conjecture*, dated 6 Feb 2026. It lists the conjecture as open. This was read
   earlier in this swarm run through a summarizing web tool, not from the raw
   page, so it is secondary evidence only.
4. J. Harlander, S. Rosebrock, *The Local Structure of Injective LOT-Complexes*,
   arXiv:2207.07991v2 (updated 2023-07-31). The abstract says: "Labeled oriented
   trees, LOT's, encode spines of ribbon discs in the 4-ball and ribbon 2-knots
   in the 4-sphere. The unresolved asphericity question for these spines is a
   major test case for Whitehead's asphericity conjecture." This bears directly
   on section 3. The input Kawauchi needs (every ribbon disk-link exterior is
   aspherical) contains the asphericity of these spines, which this abstract
   calls unresolved. The graph carries that as `labeled-oriented-trees-are-aspherical`
   (OPEN).
5. Claimed resolutions. The arXiv listings show no journal reference for any of
   them.
   - A. Kawauchi, *Whitehead aspherical conjecture via ribbon sphere-link*,
     arXiv:2303.04368 (v1 2023-03-08, v2 2024-04-09). The abstract says: "In this
     paper, by generalizing this argument, this conjecture is confirmed to be
     true for every aspherical 2-complex." e-print source read; see section 3.
   - A. Kawauchi, *Ribbonness of Kervaire's sphere-link in homotopy 4-sphere and
     its consequences to 2-complexes*, arXiv:2212.02617 (v1 2022-12-05, v3
     2024-03-28). The abstract says: "In the use of the smooth unknotting
     conjecture and the smooth 4D Poincaré conjecture, ..." and "it is shown that
     the compact complement of every ribbon disk-link in the 4-disk is
     aspherical". It claims the finite contractible case. e-print source read,
     cited below as [KA] with line numbers of the fetched `.tex`.
   - E. Pasku, *An answer to the Whitehead asphericity question*,
     arXiv:2107.12293v1 (26 Jul 2021). The abstract claims: "if P=(x,r) is an
     aspherical presentation of the trivial group, and r_0 ∈ r a fixed relation,
     then P_1=(x,r_1) is aspherical". That is the removal of one 2-cell from a
     contractible presentation complex, the type-(a) case. Only the abstract was
     read. Even if correct, it would settle only type (a). In the paraphrased
     wording, type (b) is the whole conjecture (section 4).
6. Context, not status evidence.
   - A. Conway, *Homotopy ribbon discs with a fixed group*, arXiv:2201.04465v3,
     Algebr. Geom. Topol. 24 (2024) 4575–4587. The abstract classifies
     "exteriors of aspherical homotopy ribbon discs" and carries asphericity as a
     hypothesis.
   - J. Harlander, S. Rosebrock, *Ribbon 2-knot groups of Coxeter type*,
     arXiv:2103.01987, Algebr. Geom. Topol. 23 (2023) 2715–2733. The abstract
     calls LOT presentations "a well known and important testing ground for the
     validity (or failure) of Whitehead's asphericity conjecture".
7. Older status evidence, read from sources on 2026-09-16.
   - A. N. Barreto, E. G. Minian, arXiv:2308.07447v1 (PDF stamp 14 Aug 2023).
     Source line 134: "Local indicability of LOT groups is an open problem
     (that would imply asphericity of the associated presentations)."
   - A. M. Mikhovich, arXiv:2105.00281v2 (PDF stamp 16 Sep 2021). The
     introduction says the conjecture "is still an open problem".

**Not re-verified this session.**
- The status of the smooth 4D Poincaré conjecture and the smooth unknotting
  conjecture for `S^2`-links. [KA] line 172 says: "The positive proofs of these
  conjectures are in \cite{K4} and \cite{K1,K2,K3}, respectively." Those are
  the author's own manuscripts, not read. To my knowledge SPC4 is open, but I
  did not re-check that on 2026-09-16, so this is unverified.
- Howie 1983 (Topology 22, 475–485), Howie 1985 (Trans. AMS 289, 281–302) and
  Luft 1996 were not read. For their content the graph relies on the secondary
  pins in `howie-3-deformation-lot-citation`.

## 3. Audit of the claimed proofs

Line numbers below refer to the `.tex` e-print sources fetched 2026-09-16:
- `[W]` is arXiv:2303.04368, `main.tex`, 825 lines.
- `[KA]` is arXiv:2212.02617, 1016 lines.

### 3.1 The chain in [W]

The chain runs from the headline claim down to one finite input.

- **Headline.** [W] Theorem 1.1 (l.88): "Whitehead Aspherical Conjecture is true."
  - Its proof (l.769–772) combines Corollary 5.3 with two implications between
    Conjectures 3, 2 and 1.
  - Those implications are the elementary compactness and covering reductions of
    [W] sections 2–3.
- **Corollary 5.3** (l.748): "Every subcomplex of every homology-trivial
  unit-group presentation is aspherical."
  - Its proof (l.752–761) needs `E(L^D \ K^D)` to be aspherical "by Lemma 5.1"
    (l.758).
  - Here `L^D \ K^D` is an arbitrary sublink of a free ribbon disk-link, so it is
    not free in general.
- **Lemma 5.1** (l.622–626): "The closed exterior E(L^D) of every (possibly
  infinite) ribbon disk-link L^D in H^4 is aspherical."
  - It is announced at l.617–618 as "an infinite version of the results of
    \cite[Theorem~1.4, Lemma~3.2]{KA}".
  - The proof reduces to a finite ribbon disk-link `\bar L^D_+` (l.664–665), not
    assumed free, and says at l.666: "Since $E(\bar L^D_+)$ is aspherical by
    \cite[Lemma~3.2]{KA}".
- **Citation mismatch.** [KA] Lemma 3.2 (l.494–500) is only about *free* ribbon
  disk-links. The finite statement actually needed is [KA] Theorem 1.4 (l.304–305):
  "The compact complement $E(K^D)$ of every ribbon disk-link $K^D$ in the 4-disk
  $D^4$ is aspherical."
- **Secondary gap, not pursued.**
  - l.675 asserts "$f^+(D^{q+1})\cap {\mathbf b}_+^2=\emptyset$".
  - But `f^+` lands in `Int E(L^D_+)` with `L^D_+ = \tilde D_+ ∪ \tilde b^1_+`
    (l.657, 671), which does not exclude `b_+^2`.
  - No argument is given.
- **Theorem 5.2** (l.712–722). The homotopy-equivalence part is "similar to the
  proof of \cite[Theorem~1.3]{KA}" (l.728).

So, restricted to finite complexes, [W] rests on [KA] Theorems 1.3 and 1.4.

### 3.2 The chain in [KA]

- **Corollary 1.6** (l.328–329): "Every connected subcomplex of every
  contractible finite 2-complex is aspherical." It is derived from Theorems 1.3
  and 1.4 (l.321–324).
- **Theorem 1.3** (ribbon disk-link presentations, l.288–296). Its proof (section
  4.1, l.563–601) uses Theorem 1.1 (l.591), Lemma 3.1 (l.595) and Lemma 3.2
  (l.598).
- **Lemma 3.2** uses Lemma 2.1 (l.513) and the imitation theory of [K0].
- **Lemma 2.1** uses the smooth 4D Poincaré conjecture at l.363 and "Smooth
  Unknotting Conjecture for an $S^2$-link" at l.368.
- **Theorem 1.1** (l.183 ff.), in its proof (l.391–453):
  - identifies homotopy 4-spheres with `S^4` (l.404–405, under the global
    convention of l.173);
  - uses the Free Ribbon Lemma (l.412), whose proof uses Lemma 2.1 (l.748).
- **Theorem 1.4** is proved in section 5.1 (l.614–703) using Lemma 3.2 (l.620),
  Theorem 1.3 (l.622), "the proof of Theorem~1.1 and Lemma~3.1" (l.651), [KSS I]
  normal forms (l.632, l.672) and the Horibe–Yanagawa lemma (l.696).
- **Status of Theorem 1.4.** It is Howie's ribbon disc complement conjecture, as
  [KA] itself says at l.309–310: "The asphericity of the compact complement of a
  ribbon disk-knot in $D^4$ has been conjectured by Howie \cite{Howie}". By the
  secondary pins in `howie-3-deformation-lot-citation`, LOT complexes are spines
  of ribbon disc complements. So Theorem 1.4 contains
  `labeled-oriented-trees-are-aspherical`, which arXiv:2207.07991v2 calls
  "unresolved".

### 3.3 The argument for [KA] Theorem 1.4, step by step

Let `K^D` be a ribbon disk-link and `S(*)` an immersed 2-sphere in `E(K^D)`.

- **(0) "It suffices" (l.617–622).** It suffices to find a free ribbon disk-link
  `L^D ⊃ K^D` disjoint from `S(*)`. Then `S(*) ⊂ E(L^D)`, and `pi_2(E(L^D)) = 0`
  by Lemma 3.2.
  - Up to homotopy of `S(*)` in `E(K^D)`, this is *equivalent* to Theorem 1.4,
    granted [KA] Theorem 1.1.
  - If `E(K^D)` is aspherical, `S(*)` is nullhomotopic, so it is homotopic into a
    small ball missing any given `L^D`.
  - So step (0) is a reformulation, not a reduction.
- **(i) Normal form (l.669–689).**
  - Neighbourhoods of the double points of `S(*)` are pulled down into
    `R^3[0]`.
  - A joint normal form of `K^D ∪ S(*)` is asserted "(see \cite[I]{KSS})":
    - `S(*)` has maximal discs `d^{S(*)}` at `t = 2` and bands `b^{S(*)}` at
      `t = 1`;
    - at `t = 0` it has a split union `e^{S(*)}` of Hopf disk pairs and discs;
    - l.689: "By construction, note that $e^{S(*)}$ is split from $k^D$."
- **(ii) Moving `d^C` (l.690–694).** "By an isotopic move of the union of the disk
  system $d^C$ and a neighborhood of the arc system $b_*\cap d^C$ in $b_*$ in
  ${\mathbf R}^3$ keeping the disk system $d_*$ fixed, it can be assumed that
  $d^C\cap(d_*\cup e^{S(*)}\cup b^{S(*)})=\emptyset$."
  - No further justification is given.
  - The moved region contains pieces of the bands `b_*` of `K^D` itself.
- **(iii) Horibe–Yanagawa (l.696–701).** The disc systems bounded by the trivial
  link `o_* ∪ o^{S(*)} ∪ o^C` may be replaced by any disjoint disc systems
  without changing `K^D ∪ S(*)` or `L^D` up to ambient isotopy fixing `R^3[0]`.
  - Given (i) and (ii), I see no formal problem with this step.
  - The lemma's statement in [KSS] was not read.
- **(iv) Conclusion (l.701–702).** `S(*) ⊂ E(L^D) ⊂ E(K^D)`.

### 3.4 The argument never uses sphericity; its torus version is false

**Where sphericity enters.** In section 5.1 the hypothesis that `S(*)` is a
2-sphere is used in one place only: the final deduction at l.618–622, where
`S(*) ⊂ E(L^D)` and `pi_2(E(L^D)) = 0` make `S(*)` nullhomotopic. The
construction of `L^D` disjoint from `S(*)` cites only the following.

- The existence of a free extension `L^D = K^D ∪ C^D` in normal form (l.651–668),
  "By the proof of Theorem~1.1 and Lemma~3.1". This does not involve `S(*)` at
  all.
- Pulling neighbourhoods of double points down to `R^3[0]` (l.669–671). This is
  a finger move along arcs. Generic arcs miss a surface in a 4-manifold, so it
  works for any generically immersed closed surface.
- The [KSS I] normal form (l.672–689). Its shape does not depend on the genus:
  maximal discs `d^{S(*)}`, bands `b^{S(*)}`, and a split system of Hopf disc
  pairs and discs at `t = 0`. Only the numbers of discs and bands do.
- The isotopic move of step (ii) (l.690–694), for which no argument is given.
- The Horibe–Yanagawa lemma (l.696), a statement about disc systems bounded by a
  trivial link in `R^3`.

None of these refers to the domain of `S(*)`. So the same text, with "immersed
2-sphere" replaced by "immersed torus", asserts the following.

> **(G_T)** Let `K^D` be a ribbon disk-link in `D^4` and `f : T^2 -> Int E(K^D)`
> a generic immersion. Then, after a homotopy of `f` in `E(K^D)`, there are an
> ambient isotopy of `D^4` fixing `S^3`, ending at `h`, and a free ribbon
> disk-link `L^D ⊃ h(K^D)` with `h(f(T^2)) ∩ L^D = ∅`.

The isotopy is the one allowed at l.698–700: "ambient isotopies (with compact
supports) of ${\mathbf R}^3[0,+\infty)$ keeping ${\mathbf R}^3[0]$ fixed".

**Proposition A.** If (G_T) holds for a ribbon disk-link `K^D`, then every map
`g : T^2 -> E(K^D)` has cyclic image `g_*(pi_1 T^2)`. The image is defined up
to conjugacy, and cyclicity is invariant under conjugation.

*Proof.*
1. Push `g` into the interior along a collar. A generic smooth map from a closed
   surface to a 4-manifold is an immersion with transverse double points. So
   `g` is homotopic to an `f` as in (G_T).
2. Apply (G_T), and rename the homotoped map `f`. The compact set `h(f(T^2))`
   misses `L^D`, so `h∘f` maps into `D^4 - L^D ⊂ D^4 - h(K^D)`.
3. By [KA] l.234–235, a free ribbon disk-link is one with `pi_1(D^4 - L^D)`
   free. The image of `Z^2` in a free group is an abelian subgroup, hence
   cyclic. Its image in `pi_1(D^4 - h(K^D))` is a quotient of a cyclic group, so
   it is cyclic too.
4. `h` is a homeomorphism `D^4 - K^D -> D^4 - h(K^D)`, and the inclusion
   `E(K^D) ⊂ D^4 - K^D` is a homotopy equivalence. So `g_*(pi_1 T^2)` is
   cyclic. ∎

**Proposition B.** There is a ribbon disk-knot `K^D` in `D^4` with
`pi_1(D^4 - K^D) ≅ B_3 = <x, y | xyx = yxy>`, and a map `g : T^2 -> E(K^D)`
that is injective on `pi_1`.

*Proof.* The realization in step 1 is recalled standard material, not
re-verified from a source this session. Steps 2 and 3 are complete.

1. **Realization.** Any one of the following gives such a `K^D`.
   - **Band form.** In the definition at [KA] l.220–223, take two trivial discs
     and one band in `S^3` joining their boundaries. The group has the
     presentation `<x_1, x_2 | x_2 = w x_1 w^{-1}>`, where `w` records the
     signed passages of the band through the two spanning discs. Every word `w`
     is realized. For `w = x_1 x_2` the relation becomes
     `x_2 x_1 x_2 = x_1 x_2 x_1`, which is `B_3`.
   - **Product form.** Let `A ⊂ B^3` be a properly embedded trefoil arc. Then
     `A × I ⊂ B^3 × I ≅ D^4` is a proper disc after smoothing corners.
     - Its exterior is `(B^3 - N(A)) × I`, homotopy equivalent to the trefoil
       exterior, so its group is the trefoil group `B_3`. This part is
       elementary.
     - That `A × I` is ribbon in Kawauchi's sense is recalled.
   - **LOT form.** Drop one relator from the Wirtinger presentation of the
     trefoil. This gives `<x_1, x_2, x_3 | x_1 x_2 = x_2 x_3, x_2 x_3 = x_3 x_1>`.
     - Its LOT has edges 1–3 (label 2) and 2–1 (label 3), which form a tree.
     - Substituting `x_3 = x_2^{-1} x_1 x_2` gives `x_2 x_1 x_2 = x_1 x_2 x_1`.
     - By the secondary pin in `howie-3-deformation-lot-citation`, "LOT
       complexes are 2-dimensional spines of ribbon disc complements".
2. **`Z^2 ⊂ B_3`.**
   - **Δ² is central.** Put `Δ = xyx`. Then `Δx = xyxx` and `yΔ = (yxy)x = xyxx`,
     so `Δx = yΔ`. Similarly `Δy = x(yxy) = xxyx = xΔ`. Hence `Δ^2 x = Δ y Δ = x Δ^2`
     and `Δ^2 y = y Δ^2`.
   - **A representation.** Let `ρ(x) = A = [[1,1],[0,1]]` and
     `ρ(y) = B = [[1,0],[-1,1]]`. Direct multiplication gives
     `ABA = BAB = [[0,1],[-1,0]]`, so `ρ` is a homomorphism `B_3 -> SL(2,Z)`, and
     `ρ(Δ)^2 = -I`.
   - **Injectivity.** Suppose `x^a Δ^{2b} = 1`.
     - Applying `ρ` gives `(-1)^b [[1,a],[0,1]] = I`, so `a = 0`.
     - Abelianization `x, y -> 1` sends `Δ^2` to 6, so `a + 6b = 0`, and `b = 0`.
     - So `(a, b) -> x^a Δ^{2b}` is an injective homomorphism `Z^2 -> B_3`.
3. **The torus map.**
   - Give `T^2` one 0-cell, 1-cells `α` and `β`, and one 2-cell attached along
     `αβα^{-1}β^{-1}`.
   - Send `α` and `β` to loops representing `x` and `Δ^2`. The attaching loop
     goes to a representative of `[x, Δ^2] = 1`, so the map extends over the
     2-cell.
   - By step 2, `g_*` is injective. ∎

**Consequence.**
- By Propositions A and B, (G_T) fails for the `B_3` ribbon disc.
  - So for immersed tori at least one of steps (i)–(iii) is false, with the
    justifications [KA] gives.
  - Those justifications do not tell tori and spheres apart. So section 5.1 does
    not prove [KA] Theorem 1.4 as written. A repair would have to use sphericity
    inside the construction of `L^D`, or build `L^D` another way.
- The obstruction depends only on the homotopy class of `g`. So no choice of
  generic position, normal form or band moves rescues the torus version.
- This is not a counterexample to Theorem 1.4 or to the conjecture. The exterior
  of the `B_3` disc is homotopy equivalent to the trefoil exterior, which is
  aspherical (a standard fact, recalled). The test refutes a genus-blind
  *argument*, not a statement.
- **Which step fails** was not located. Everything downstream of step (ii) does
  follow from it.
  - l.695 (triviality of `o_* ∪ o^{S(*)} ∪ o^C`) follows from l.694.
    - `o_* ∪ o^{S(*)}` bounds the disjoint discs `d_* ∪ d^{S(*)}`, so it is trivial.
    - `o^{S(*)}` lies in `e^{S(*)} ∪ b^{S(*)}`, so l.694 makes `d^C` a disc system
      missing `o_* ∪ o^{S(*)}`.
    - Shrinking `d^C` into small balls splits `o^C` off as unknots.
  - Step (iii) then gives a configuration isotopic to `K^D ∪ S(*)`, containing a
    free ribbon disk-link isotopic to `L^D` and disjoint from the surface.
  - So the prime suspect is **step (ii)**. It is the only place where the free
    extension `C^D` is moved relative to `S(*)`, and it moves pieces of `K^D`'s
    own bands `b_*`, with no argument.
  - A second suspect is not verified. In step (i), the normal forms of `C^D` and
    of `S(*)` are both asserted to extend *the same* normal form of `K^D`. I did
    not check that this is achievable.

### 3.5 Consequences for the graph

- The graph has no route importing this conjecture from Kawauchi.
  - The Kawauchi nodes concern Kervaire–Laudenbach:
    `kawauchi-weak-kervaire-rests-on-unresolved-inputs` (which invalidates
    `kl-via-weak-conjecture-import`) and its route `kawauchi-dependency-audit`.
- A Whitehead import through [W] would be dead on two independent counts.
  1. It declares dependence on the smooth 4D Poincaré and smooth unknotting
     conjectures (the house rule in `kawauchi-dependency-audit`).
  2. Even granting those inputs, the argument for [KA] Theorem 1.4 is incomplete
     as written (3.4). Theorem 1.4 is Howie's ribbon disc complement conjecture,
     which contains `labeled-oriented-trees-are-aspherical`.
- `kawauchi-weak-kervaire-rests-on-unresolved-inputs` says: "Should the
  four-dimensional inputs be independently settled, the right move is to
  re-audit". For the asphericity half of [KA] (Theorem 1.4, Corollary 1.6),
  3.4 is that re-audit in advance: settling the 4D inputs would not repair
  section 5.1.
  - I did not read arXiv:2303.13728, so I make no claim about whether the
    Kervaire chain uses Theorem 1.4.

## 4. Wedge construction: every counterexample gives a type-(b) chain

**Lemma W.** Let `L` be a contractible 2-complex and `A ⊂ L` a finite connected
subcomplex with `pi_2(A) ≠ 0`. Then there is a contractible 2-complex `M` with the
following properties.

- `M` is the union of a chain `K_0 ⊂ K_1 ⊂ ...` of finite connected subcomplexes.
- `K_0 ≅ A`.
- Every `K_n` has `pi_2(K_n) ≠ 0`.
- Every inclusion `K_n -> K_{n+1}` is nullhomotopic.

*Proof.*
1. **Setup.** Fix a vertex `a ∈ A`. For `i ≥ 0` let `L^(i) ⊃ A^(i) ∋ a^(i)` be
   copies of `L ⊃ A ∋ a`.
   - Let `M_∞` be the wedge of all `L^(i)`, with every `a^(i)` identified to one
     vertex `*`.
   - Let `M_n = L^(0) ∨ ... ∨ L^(n) ⊂ M_∞`.
2. **Each `M_n` is contractible.** Van Kampen gives `pi_1(M_n) = 1`, and reduced
   homology of a wedge at a vertex is the direct sum, so it is 0. A simply
   connected CW complex with vanishing reduced homology is contractible, by
   Hurewicz and Whitehead.
3. **Induction.** Put `K_0 = A^(0)`. Suppose `K_n ⊂ M_n` is finite, connected,
   and contains `*` and `A^(n)`.
   - Since `M_n` is contractible, there is a nullhomotopy `H : K_n × I -> M_n` of
     the inclusion.
   - Its image is compact, connected and contains `K_n`. So it lies in a finite
     subcomplex. Let `C_n` be the component of that subcomplex containing the
     image.
   - Put `K_{n+1} = C_n ∨ A^(n+1) ⊂ M_n ∨ L^(n+1) = M_{n+1}`. It is finite and
     connected, and contains `*` and `A^(n+1)`.
4. **Nullhomotopic inclusions.** `H` lands in `C_n ⊂ K_{n+1}`.
5. **Non-asphericity.** Collapsing `C_{n-1}` to `*` retracts `K_n` onto `A^(n)`
   for `n ≥ 1`. A retract injects on `pi_2`, so `pi_2(K_n) ≠ 0`.
6. **`M = ∪ K_n` is contractible.** It is a connected subcomplex of `M_∞`, so a
   2-complex.
   - A map `S^k -> M` has compact image, so it lies in some `K_n`.
   - There it becomes freely nullhomotopic in `K_{n+1}`. A based map of a sphere
     that is freely homotopic to a constant is trivial in `pi_k`, since the
     `pi_1`-orbit of the trivial element is trivial.
   - So all homotopy groups of `M` vanish, and `M` is contractible by Whitehead. ∎

**Corollary.** Read type (b) as the Cerdeiro–Minian paraphrase in section 1 does
(with the `K_i` connected). Then the following are equivalent.

1. The Whitehead asphericity conjecture fails.
2. Some contractible 2-complex has a finite connected non-aspherical subcomplex.
3. A type-(b) chain exists.

*Proof.*
- (1) => (2) is the covering and compactness reductions of section 1.
- (2) => (3) is Lemma W.
- (3) => (1): the union of a type-(b) chain is contractible, by step 6 of the
  proof, and `K_0` is a non-aspherical connected subcomplex of it. ∎

In particular, in that wording, a type-(a) counterexample gives a type-(b) chain
by Lemma W. Removing a 2-cell from a connected 2-complex keeps it connected, so
item 2 holds.

**Caveat.** This is too easy to be Luft's 1996 theorem. The likely explanation is
that Howie's printed type (b), or Luft's formulation, constrains the chain more
than the paraphrase does. For instance it might constrain how `K_{n+1}` is built
from `K_n`; that is a guess, not checked. I did not read Howie 1983 or Luft 1996.
So I claim neither that Lemma W recovers Luft's theorem, nor that Howie's own
type (b) is equivalent to the conjecture. No novelty is claimed: Lemma W is an
elementary compactness construction and is very likely folklore.

**Practical consequence.** Any work aimed at "type (b)" should first pin Howie's
original statement (Topology 22 (1983) 475–485). In the paraphrased form, type (b)
is not a special case: it is the whole conjecture.

**Where two-dimensionality enters.** In a 2-complex there are no 3-cells, so
`H_2` of a subcomplex injects into `H_2` of the ambient complex. So every
subcomplex `A` of a contractible 2-complex has `H_2(A) = 0`. The exact sequence
of the pair also gives `H_1(A) ≅ H_2(L, A)`, a subgroup of the free abelian group
`C_2(L, A)`, so `H_1(A)` is free abelian. Section 5.3 uses both facts. Lemma W
itself uses no dimension restriction beyond reading "non-aspherical" as
`pi_2 ≠ 0`.

## 5. Approaches tried and where each dies

### 5.1 Importing the claimed proof

- **Where it dies.** At [KA] section 5.1, step (ii), as far as it can be located.
  The argument is genus-blind and its torus version is false (3.4).
- **Even if repaired,** the import would rest on the smooth 4D Poincaré and smooth
  unknotting conjectures (3.5).

### 5.2 The genus test as a filter for type-(a) arguments

The same test applies inside the program's own setting.

- **A contractible `L`.** Let `L` be the presentation complex of
  `<x, y | xyxy^{-1}x^{-1}y^{-1}, x>`.
  - `pi_1(L) = 1`: the relator `x` kills `x`, and the first relator then reduces
    to `y^{-1}`.
  - `chi(L) = 1 - 2 + 2 = 1` and `H_1(L) = 0`. `H_2(L)` is free abelian of rank
    `chi - 1 = 0`. So `L` is contractible, by Hurewicz and Whitehead.
- **The complement `K = L - e_x`.** It is the presentation complex of
  `<x, y | xyx = yxy> = B_3`, and `pi_1(K) ⊃ Z^2` by 3.4, Proposition B, step 2.
- **`K` is aspherical, so this is not a counterexample.**
  - `chi(K) = 0` and `H_1(K) = Z`, so `H_2(K) = 0`.
  - `B_3` is the trefoil group, and knot groups are locally indicable.
  - The source of Barreto–Minian, arXiv:2308.07447v1, states both facts used
    here (read 2026-09-16 from the e-print source, lines 110 and 134): "any
    connected $2$-complex $X$ with $\pi_1(X)$ locally indicable and $H_2(X)=0$
    is aspherical (see \cite{h1,h2})" and "It is well-known that knot groups
    are locally indicable (see \cite{h1})".
- **Lesson.** Suppose an argument shows that every map `S^2 -> L - e` factors, up
  to homotopy, through a space whose `pi_1` has only cyclic abelian subgroups
  (for instance a free group). If it never uses that the domain is `S^2`, it
  also shows that every `Z^2 -> pi_1(L - e)` has cyclic image, which is false
  for this `L`.
  - So any such argument must use sphericity somewhere, and a referee can ask
    where.
  - Kawauchi's section 5.1 has exactly this shape: it factors through
    `E(L^D)`, and `pi_1(E(L^D))` is free.

### 5.3 From an infinite counterexample back to type (a)

Aim: from a finite non-aspherical `A` inside a contractible 2-complex `L`, build
a type-(a) configuration.

- **A finite contractible hull.** Take a finite connected `C` with `A ⊂ C ⊂ L`,
  for instance the carrier of a nullhomotopy of `A`.
  - By section 4, `H_2(C) = 0` and `H_1(C) ≅ Z^r`.
  - Attach `k` 1-cells and `m` 2-cells to get a finite `L'`. If `pi_1(L') = 1`,
    then `H_2(L')` has rank `chi(L') - 1 = m - r - k`. So `L'` is contractible if
    and only if `m = r + k`.
  - So a hull of this kind exists if and only if, for some such `C` and some `k`,
    the group `pi_1(C) * F_k` is normally generated by `r + k` elements.
    Abelianization forces at least `r + k`.
  - This is a weight problem of Kervaire–Wiegold type. I could not settle it for
    general `C`, and this is where the attempt dies first.
- **Even with a hull.** Suppose `L' ⊃ A` is finite and contractible. Remove the
  2-cells of `L'` not in `A` one at a time.
  - Some first stage `X_j = X_{j-1} - e` is non-aspherical while `X_{j-1}` is
    aspherical.
  - `X_{j-1}` is in general not contractible. Passing to its universal cover
    restores contractibility but loses finiteness.
  - So this only reproduces the infinite situation, and by Lemma W the infinite
    situation is already the whole conjecture.
  - Howie's 1983 argument for type (a) presumably proceeds differently; not read.

### 5.4 Routes already in the graph, not re-attacked

- **Bestvina–Brady.** The route is
  `nonaspherical-subcomplex-via-bestvina-brady-kernel`. Its open input is
  `bestvina-brady-poincare-kernel-has-geometric-dimension-two`.
- **One-cell L² chain.** Its open inputs are
  `one-cell-complement-groups-have-vanishing-first-l2-betti` and
  `non-ascending-one-cell-complements-have-vanishing-l2-b1`.
  - The Fisher–Lodha counterexamples (section 2, item 1) are not finitely
    generated. So they do not touch these finitely presented statements.
- Nothing was added to either route this session.

## 6. Graph decisions and what remains open

**No `research/` node was written.**

1. **Section 3.** It is a body-level audit of unrefereed preprints. Its rigorous
   core, Propositions A and B, bears on no claim now in the graph.
   - No node imports this conjecture, or the ribbon disc complement conjecture,
     from Kawauchi.
   - The Kervaire-side audit already stands on declared dependencies.
   - README rule 5 says "do not create an unrelated Cairn node merely to archive
     it. Off-axis reconnaissance belongs in `notes/`". So it stays here.
   - **Recommendation.** Someone may propose importing, from arXiv:2303.04368 or
     arXiv:2212.02617, this conjecture, `labeled-oriented-trees-are-aspherical`,
     or Howie's ribbon disc complement conjecture. Section 3.4 is the reason
     that import cannot be established, even after the smooth 4D Poincaré and
     unknotting conjectures are settled.
2. **Section 4.** Lemma W shows that paraphrase-worded type-(b) chains are
   equivalent to `nonaspherical-subcomplex-of-contractible-2-complex-exists`.
   - A node would restate that claim.
   - The statement a node would actually need, Howie's original type (b), is not
     pinned.

**Nothing else touched.** Beyond this note, the only actions in the repository
were taking and releasing the lock.

**What remains open.**
- `whitehead-asphericity-conjecture`: OPEN. The literature gate is in section 2.
- The finite one-cell case `contractible-2-complex-minus-a-cell-is-aspherical`
  (type (a)): OPEN.
- Type (b) in the paraphrased wording is the whole conjecture (section 4).
  - Howie's original type (b) is not pinned.
  - Pinning it from Topology 22 (1983) 475–485, together with Luft, Math. Proc.
    Camb. Phil. Soc. 119 (1996) 493–495, is a concrete literature task.
- Howie's ribbon disc complement conjecture, and
  `labeled-oriented-trees-are-aspherical`: OPEN. The only claimed proof I found
  is incomplete as written (3.4).
  - arXiv:2207.07991v2 (2023) calls LOT asphericity "unresolved".
  - arXiv:2308.07447v1 (2023), source line 134, calls local indicability of LOT
    groups "an open problem (that would imply asphericity of the associated
    presentations)".
- **Suggested next attack on [KA] section 5.1.** Run step (ii) by hand on the
  product-form `B_3` disc `A × I` with an embedded peripheral torus
  `T ⊂ (B^3 - N(A)) × {1/2}`.
  - `T` is embedded, so there are no Hopf disc pairs.
  - The attempt to move `d^C` off `e^T ∪ b^T` must fail somewhere. Seeing where
    would turn "incomplete as written" into a located error.

## 7. Sources

All accessed 2026-09-16 unless marked.

**Read at source level (e-print `.tex`).**
- A. Kawauchi, arXiv:2303.04368v2 (v1 2023-03-08, v2 2024-04-09), `main.tex`,
  825 lines. Cited as [W].
- A. Kawauchi, arXiv:2212.02617v3 (v1 2022-12-05, v3 2024-03-28), 1016 lines.
  Cited as [KA]. The definitions at l.173–242, Lemma 3.2 at l.494–544, and
  sections 4.1 and 5.1 at l.563–703 were read in full.
- M. A. Cerdeiro, E. G. Minian, *A new approach to Whitehead's asphericity
  question*, arXiv:1203.5348v1, source lines 107–114 (Howie's reduction and the
  Luft sentence).
- A. N. Barreto, E. G. Minian, *Local indicability of groups with homology circle
  presentations*, arXiv:2308.07447v1. The PDF stamp reads 14 Aug 2023. Source
  lines 110, 112 and 134 were read.

**Read from PDF text.**
- A. M. Mikhovich, *Rational and p-adic analogs of J.H.C. Whitehead's
  conjecture*, arXiv:2105.00281v2. The PDF stamp reads 16 Sep 2021.
  - Introduction: the conjecture "is still an open problem". This is 2021 status
    evidence, superseded by the 2025–2026 items of section 2.

**Abstract pages or arXiv API metadata.**
- arXiv:2608.25988v1 (2026-08-26).
- arXiv:2511.15212v2 (v1 2025-11-19, v2 2026-05-31).
- arXiv:2107.12293v1 (2021-07-26).
- arXiv:2207.07991v2 (2023-07-31).
- arXiv:2201.04465v3, journal ref Algebr. Geom. Topol. 24 (2024) 4575–4587.
- arXiv:2103.01987v1, journal ref Algebr. Geom. Topol. 23 (2023) 2715–2733.

**Secondary.**
- google-deepmind/formal-conjectures issue #2189 (dated 2026-02-06), read through
  a summarizing web tool.

**Graph files read.**
- `research/README.md` rule 5.
- `nonaspherical-subcomplex-of-contractible-2-complex-exists`.
- `l2-normal-rank-bound-fails-for-torsion-free-groups`.
- `kawauchi-weak-kervaire-rests-on-unresolved-inputs`.
- `kawauchi-dependency-audit`.
- `howie-3-deformation-lot-citation`.
- `labeled-oriented-trees-are-aspherical`.
- The route and claim ids listed in section 1, checked to exist.

**Not read (unverified beyond bibliographic lines).**
- J. Howie, Topology 22 (1983) 475–485.
- J. Howie, Trans. AMS 289 (1985) 281–302.
- E. Luft, Math. Proc. Camb. Phil. Soc. 119 (1996) 493–495.
- Kawauchi–Shibuya–Suzuki, *Descriptions on surfaces in four-space I*.
- Kawauchi's manuscripts cited in [KA] as K0–K5.
- arXiv:2303.13728.

**Recalled standard facts, not re-verified from a source this session.**
- The band presentation of ribbon disc groups, and the realizability of every
  band word.
- Ribbonness of the product disc `A × I`.
- Asphericity of knot exteriors.
- Genericity of immersions `T^2 -> M^4`.
- Abelian subgroups of free groups are cyclic.

## Referee (2026-09-16)

**Verdict: sound; notes only, landed as is plus this section.** No `research/`
node was written, and I agree with that. The rigorous core (3.4) is about an
external, unrefereed argument, and it bears on no graph claim. README rule 5
puts that material in `notes/`. The root claim stays OPEN.

**What I checked.**
- **Quotes against the saved sources.** I checked the solver's scratch copies of
  the e-prints: arXiv:2212.02617 `.tex` (1016 lines) and arXiv:2303.04368
  `main.tex` (825 lines). All of these match the note:
  - [KA] l.172, l.218–242 (definitions; free means `pi_1` free), l.304–310
    (Theorem 1.4, Howie attribution) and l.494–500 (Lemma 3.2, free links only);
  - all of section 5.1, l.614–703, including the step (ii) sentence;
  - [W] l.88, l.617–626, l.664–667, l.675, l.748 and l.758.
  I re-read section 5.1 in full. The normal form of `K^D ∪ S(*)` has minimal
  (Hopf) discs, one band level and maximal discs. Its shape does not depend on
  genus, and I found no place where the text uses that the surface is a sphere.
  So the textual premise of (G_T) holds up.
- **Literature items.** I checked the saved arXiv abstract pages and sources:
  - 2608.25988: title, authors, date 2026/08/26, and the quoted phrases "an
    important special case of the Whitehead asphericity conjecture", "This
    disproves the conjecture" and "not finitely generated";
  - 2511.15212: "last revised 31 May 2026 (this version, v2)";
  - 2107.12293: the Pasku statement about removing one relator;
  - Cerdeiro–Minian source: Howie's (a)/(b) and the Luft sentence, verbatim;
  - Barreto–Minian source l.110 and l.134, verbatim.
  I could not re-fetch arXiv live (proxy timeouts). The GitHub issue #2189 is
  outside this session's allowed repositories, so it stays secondary and
  unverified.
- **Proposition A.** Correct.
  - Generic maps `T^2 -> M^4` are immersions with transverse double points: the
    rank-drop locus has codimension 3 > 2.
  - The homotopy and isotopy allowed in (G_T) are handled.
  - Abelian subgroups of free groups are cyclic.
- **Proposition B, step 2.** Recomputed.
  - `ABA = BAB = [[0,1],[-1,0]]` and `(ABA)^2 = -I`.
  - `Δx = yΔ`, `Δy = xΔ`, and `Δ^2` is central.
  - The injectivity argument (SL(2,Z) image forces `a = 0`, abelianization then
    forces `b = 0`) is correct.
- **Proposition B, step 1.**
  - The band word `w = x_1x_2` gives the relator `x_2^{-1} x_1 x_2 x_1 x_2^{-1} x_1^{-1}`,
    that is `x_1x_2x_1 = x_2x_1x_2`. Checked by free reduction.
  - The LOT substitution checks.
  - The product disc `A × I` is the standard ribbon disc for `K # -K`, and its
    exterior deformation retracts to the knot exterior. This is standard, and I
    agree that it is only recalled.
- **Lemma W and its corollary.** Correct as stated:
  - the retraction `K_n -> A^(n)` collapsing `C_{n-1}` exists because
    `C_{n-1} ∩ A^(n) = {*}`;
  - a freely nullhomotopic based sphere is trivial in `pi_k`;
  - compact images lie in finite subcomplexes.
  The note's caveats are appropriate: no novelty is claimed, and Howie's printed
  type (b) is not pinned.
- **Sections 4 and 5.**
  - The 2-dimensionality facts are correct: `H_2(A) ↪ H_2(L)`, and
    `H_1(A) ≅ H_2(L,A)` is free abelian.
  - The example `<x,y | xyxy^{-1}x^{-1}y^{-1}, x>` is contractible.
  - The hull count `rank H_2(L') = m - r - k` is correct.
- **Graph ids.** All 17 ids cited in section 1, 3.5 and 5.4 exist in `research/`.
  No existing node imports arXiv:2212.02617 or arXiv:2303.04368 for asphericity.

**Scope reminders.**
- 3.4 shows that section 5.1 of [KA] is incomplete as written. It does not
  locate the failing step: "step (ii) is the prime suspect" is a judgement. It
  refutes nothing.
- Proposition B's realization step rests on recalled standard facts, which the
  note labels as recalled.

**Not landed.** `experiments/whitehead-three-generator-census-2026-09-16/` is in
the working tree. It is not listed in the report, not mentioned in this note,
was still being modified after the note was written, and matches the active
lock on `contractible-2-complex-minus-a-cell-is-aspherical`. I treated it as
another agent's in-flight work and did not land or touch it.
