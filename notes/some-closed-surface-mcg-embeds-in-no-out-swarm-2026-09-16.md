# Zaremsky 3.10(b), hole `some-closed-surface-mcg-embeds-in-no-out-free-group` (swarm, 2026-09-16)

Agent `swarm-some-closed-surface-mcg-embeds`. The hole was locked for this session
and is unlocked at the end. Nothing here is committed by the agent; the referee
lands it.

## Setup

- **Chain.** `zaremsky-3-10-out-fm-embeds-in-aut-fn` ->
  `zaremsky-3-10b-closed-mcg-in-some-out-fn-resolved` -> route `zaremsky-3-10b-by-no`
  -> this hole. The hole also feeds `closed-mcg-no-aut-embedding-via-no-out-embedding`.
- **Hole.** Some `g` such that `MCG(S_g)`, the orientation-preserving mapping class
  group of the closed orientable genus-`g` surface, embeds in no `Out(F_n)`.
  Necessarily `g ≥ 3` (`low-genus-closed-mcgs-embed-in-aut-free-groups`).
- **Known before this session.**
  - Any host has `n ≥ 2g − 1`, by virtual cohomological dimension
    (`rank-lower-bounds-for-free-group-hosts-of-out-fm-and-mcg`).
  - The hole's Attempts record dimension, Aramayona--Souto for mapping class group
    targets, and torsion.
  - Embeddability in some `Aut(F_n)` is shared by a group and all its finite-index
    subgroups (`aut-free-embeddability-passes-to-finite-index-overgroups`); for Out
    hosts that is not known.
  - Whether finite-index subgroups of `MCG(S_g)`, `g ≥ 3`, embed in punctured-surface
    mapping class groups is open (`closed-mcgs-virtually-embed-in-punctured-mcgs`).
    A yes there would give a yes for 3.10(b) and (c), through
    `punctured-surface-mcgs-virtually-embed-in-aut-free-groups` and the lemma above.
- **The model to beat.** The bordered group `MCG(S_{g,1})` embeds in `Aut(F_{2g})`
  (Dehn--Nielsen--Baer) and hence in `Out(F_{2g+1})`. Any obstruction for closed
  surfaces must fail for this group. So it must use something the closed group has
  and the bordered group lacks: the boundary twist becomes trivial, and the chain
  relations produce torsion.

## What this session establishes

### 1. Dehn twists map to polynomially growing outer automorphisms

- **Nodes.** Claim `closed-mcg-twists-map-to-polynomially-growing-outer-autos`, route
  `closed-mcg-twists-map-to-polynomially-growing-outer-autos-proof` (`requires: []`),
  artifact `research/artifacts/closed-mcg-twists-polynomial-growth-2026-09-16.md`.
- **Statement.** Let `g ≥ 3`, `Γ ≤ MCG(S_g)` of finite index (including `Γ = MCG(S_g)`),
  and `φ : Γ → Out(F_n)` any homomorphism. If `c_1, …, c_r` are pairwise disjoint and
  `T_{c_i}^{k_i} ∈ Γ`, `k_i ≠ 0`, then `φ(⟨T_{c_1}^{k_1}, …, T_{c_r}^{k_r}⟩)` consists of
  polynomially growing outer automorphisms. Some positive power of each
  `φ(T_{c_i}^{k_i})` is in `UPG(F_n)`.
- **Engine (Lemma A).** If `ψ` is central in `D ≤ Out(F_n)` and `ψ^k ∈ [D, D]` for some
  `k ≥ 1`, then `ψ ∈ PG(F_n)`.

  Proof sketch, if `ψ ∉ PG`:
  - `L(ψ)` is a finite nonempty set of attracting laminations (BFH Lemmas 3.1.9,
    3.1.13).
  - `D` permutes `L(ψ)` by naturality, `θ_#L(ψ) = L(θψθ^{-1})`. Let `D_0` be the
    kernel, of index `m`.
  - The transfer `D → D_0^{ab}` sends the central `ψ` to `ψ^m`, so `ψ^{mk} ∈ [D_0, D_0]`.
  - The BFH expansion-factor homomorphism `PF_{Λ^+} : Stab(Λ^+) → Z` (Corollary 3.3.1)
    therefore vanishes on `ψ^m`, which forces `Λ^+ ∉ L(ψ^m) = L(ψ)`. Contradiction.
- **Surface input.** For `h ≥ 2` the boundary twist of `S_{h,b}` is central and lies
  in the commutator subgroup. A lantern whose six other curves are nonseparating gives
  `3t = [T_∂] + 3t` in the abelianization. A nonseparating curve of `S_g` has
  complement `S_{g−1,2}`; a separating one has a side of genus `≥ 2` when `g ≥ 3`.
  For finite-index `Γ`, transfer from the subsurface group `C` to the normal core of
  `Γ ∩ C` puts `T_c^m` in the commutator subgroup of that core.
- **Why genus three.** `MCG(S_{1,1})^{ab} ≅ Z`, with the boundary twist of class 12,
  so Lemma 4 of the artifact fails for `h = 1`; `MCG(S_2)` embeds.
- **Pattern.** This is Bridson's pattern for semisimple actions on CAT(0) spaces
  (twists are elliptic), transplanted to Out(F_n) with the expansion factor
  homomorphism in place of translation length. No novelty is claimed.

### 2. Korkmaz's triviality theorem, imported

- **Nodes.** Claim `closed-mcg-homs-to-aut-or-out-fn-trivial-below-rank-2g`, route
  `korkmaz-closed-mcg-free-group-hosts-citation`.
- **Statement.** For `g ≥ 3` and `n ≤ 2g − 1`, every homomorphism from `MCG(S_g)` to
  `Aut(F_n)` or `Out(F_n)` is trivial. For `g = 2` and `n ≤ 3` the image is a quotient
  of `Z/10`. Hence any host of an embedding has `n ≥ 2g` for `g ≥ 2`, one better than
  the vcd bound.
- **Source.** Korkmaz, arXiv:1104.4816v2, Theorem 5, read from the PDF.

### 3. Consequences recorded here only

- **Johnson generators.** Separating twists and bounding pair maps `T_a T_b^{-1}`
  generate the Torelli group for `g ≥ 3` (Johnson; not re-read). Under every `φ`,
  each of them goes into `PG(F_n)`, by item 2 of the claim, since `a, b` are
  disjoint. This does not make the image of Torelli a PG subgroup.
- **Aut hosts.** Through `Aut(F_n) ≤ Out(F_{n+1})`, `β ↦ [β ∗ id_t]`, the images of
  twist powers under a homomorphism to `Aut(F_n)` grow polynomially on elements of
  `F_n`: for `w ∈ F_n` the cyclic word `β^k(w) t` is cyclically reduced, so its
  conjugacy length is `|β^k(w)| + 1`, and that is polynomial in `k` for a PG class.
- **Embeddings.** In an embedding, `φ(T_c)` has infinite order, so some power is a
  nontrivial UPG element. Its image in `GL(n, Z)` is unipotent.

## Approaches tried and where they die

1. **Growth alone (item 1 above).** *Dies as an obstruction.*
   - In `MCG(S_{g,1}) ≤ Aut(F_{2g}) ≤ Out(F_{2g+1})`, Dehn twists act as Dehn twist
     automorphisms (linear growth), and the lantern argument applies verbatim there.
   - So PG images are necessary but compatible with an embedding.
2. **Dimension and rank of abelian subgroups.** *Dies at large rank.*
   - vcd gives `n ≥ 2g − 1`; Korkmaz gives `n ≥ 2g`.
   - Free abelian subgroups have rank at most `3g − 3` in `MCG(S_g)`
     (Birman--Lubotzky--McCarthy) and at most `2n − 3` in `Out(F_n)` (Culler--Vogtmann);
     both standard, not re-read. That gives only `n ≥ 3g/2`.
   - The constructions in the region go through large ranks.
3. **Bridson--Wade style arguments.** *Die.*
   - Bridson--Wade (arXiv:1004.3222v2) show higher-rank lattices map to `Out(F_n)`
     with finite image. They use two facts:
     - every nontrivial subgroup of `IA_n` maps onto `Z` (Corollary 2.9);
     - a lattice has no unbounded quasi-homomorphisms, which rules out fully
       irreducible images.
   - Both inputs fail for `MCG(S_g)`:
     - the kernel of a composite `MCG(S_g) → Out(F_n) → GL(n, Z)` can contain the
       Torelli group, whose abelianization is infinite (Johnson; not re-read);
     - `MCG(S_g)` has many unbounded quasimorphisms (Bestvina--Fujiwara; not re-read).
   - The one part that survives is the "twists die in `Z`-quotients of their
     centralizers" step, which is item 1 above.
4. **Normal subgroups.** *Dies.* Normal closures of large powers of pseudo-Anosov
   classes are free (Dahmani--Guirardel--Osin; not re-read), as are those of large
   powers of fully irreducible elements in `Out(F_n)`. Free normal subgroups do not
   separate source from host.
5. **Linear shadows.** *Dies.* A PG element has root-of-unity eigenvalues on
   `H_1(F_n)`, so twist images in `GL(n, Z)` are quasi-unipotent. The symplectic
   representation already sends twists to transvections, so this is no constraint.
6. **Torsion from chain relations.** *No contradiction found.*
   - In `S_g`, a chain of `2g + 1` curves has complement two disks. So
     `(T_{c_1} ⋯ T_{c_{2g+1}})^{2g+2} = 1`, and a chain of `2g` curves gives an element
     of order `4g + 2`.
   - Out(F_n) contains every finite group for `n` large (graph symmetries), so the
     orders only bound `n` from below, weaker than item 2.
   - The idea behind the attempt: a product of PG elements that is torsion. Nothing in
     BFH forbids a product of non-commuting PG elements from having finite order, and
     consecutive chain twists do not commute. No contradiction.
7. **Torsion normalizers.** *Untried beyond a sketch.* The hole's Attempt 3 remains:
   one would need how the normalizers of the finite subgroups above (for example the
   hyperelliptic involution's centralizer, a `Z/2` extension of a sphere braid-type
   group) sit in `Out(F_n)`. I found no route to a contradiction.

## Tentative next attack (nothing claimed)

- **Step 1.** Improve "twist images are PG" to "twist images have linearly growing
  powers" (Dehn twist automorphisms) under an embedding. Tools to look at:
  - the BFH II Kolchin theorem for UPG subgroups (not re-read);
  - the degree of polynomial growth as a conjugacy invariant, together with the
    lantern and chain relations.
- **Step 2.** For a linearly growing `ψ = φ(T_c^N)`, use its canonical efficient
  graph-of-groups splitting with cyclic edge groups (Cohen--Lustig;
  Krstić--Lustig--Vogtmann; Rodenhausen--Wade, *Centralisers of Dehn twist
  automorphisms of free groups*, Math. Proc. Cambridge Philos. Soc. 159 (2015); all
  not re-read). The centralizer of `ψ` preserves the splitting and maps to a product
  of McCool-type groups of vertex groups of smaller rank, with an abelian-by-(twist)
  kernel.
- **Step 3.** The stabilizer of `c` in `MCG(S_g)` contains `MCG(S_{g−1,2})` and maps
  into that centralizer. Korkmaz's Theorem 1 covers surfaces with boundary for linear
  representations (per his introduction, read). An Aut/Out triviality statement for
  bordered groups in rank `≤ 2(g − 1) − 1` would force the vertex actions to be
  trivial on a large subgroup.
- **Obstacle.** Vertex groups can have rank up to `n − 1`, far above `2g − 3`, so the
  induction does not close as stated. It needs a rank-drop estimate for the canonical
  splitting of a twist image.

## Literature consulted (dated 2026-09-16)

- M. Bestvina, M. Feighn, M. Handel, *The Tits alternative for Out(F_n) I*, Ann. of
  Math. 151 (2000), arXiv:math/9712217v2 (1 Mar 2000). Read from the PDF:
  - Definitions 3.1.1 and 3.1.5, Lemmas 3.1.4, 3.1.9, 3.1.10 and 3.1.13;
  - Corollary 3.3.1, re-checked verbatim this session: "There is a homomorphism
    PF_{Λ^+} : Stab(Λ^+) → Z such that ψ ∈ Ker(PF_{Λ^+}) if and only if
    Λ^+ ∉ L(ψ) and Λ^+ ∉ L(ψ^{-1})";
  - the Section 5.1 definition of PG and UPG, and the introduction's citation of
    Corollary 5.7.6.
- M. Korkmaz, *Low-dimensional linear representations of mapping class groups*,
  arXiv:1104.4816v2 (2 Aug 2011): Theorem 5 and the introduction's conventions, read.
- M. R. Bridson, R. D. Wade, *Actions of higher-rank lattices on free groups*,
  arXiv:1004.3222v2 (13 Apr 2011): Corollary 2.9 and Section 3, read.
- M. R. Bridson, K. Vogtmann, *Automorphism groups of free groups, surface groups and
  free abelian groups*, arXiv:math/0507612v1 (29 Jul 2005): Questions 15--17, read.
  They concern linearity of Out(F_3), homomorphisms from `Aut(F_n)` to mapping class
  groups, and lattices; none asks the question of this hole.
- W. Harvey, M. Korkmaz, *Homomorphisms from mapping class groups*, arXiv:math/0307107
  (9 Jul 2003). Abstract only: homomorphisms `Mod_g → Mod_h` with `g > h` are trivial
  or finite. Mapping class group targets only.
- M. Horak, *Mapping class subgroups of Out(F_n)*, arXiv:math/0310328 (revised 18 Apr
  2005). Abstract only: a covering of Outer space by Teichmüller spaces of punctured
  surfaces. Not about closed-surface embeddings.
- Bridson's theorem on semisimple actions of mapping class groups on CAT(0) spaces,
  and Farb--Margalit's *Primer* (Fact 3.7, Theorem 3.18, Proposition 5.1): used as
  recalled, not re-read.
- Search coverage. WebSearch ran on "homomorphisms mapping class group closed surface
  to Out(F_n) Dehn twists polynomially growing", on Zaremsky-problem queries, and on
  "expansion factor homomorphism" queries. The search budget of this session was then
  exhausted, so later queries did not run. No source found states the twist result;
  the novelty search is incomplete and no novelty is claimed.

## Files

- `research/closed-mcg-twists-map-to-polynomially-growing-outer-autos.md` (claim)
- `research/closed-mcg-twists-map-to-polynomially-growing-outer-autos-proof.md` (route)
- `research/artifacts/closed-mcg-twists-polynomial-growth-2026-09-16.md` (artifact)
- `research/closed-mcg-homs-to-aut-or-out-fn-trivial-below-rank-2g.md` (claim)
- `research/korkmaz-closed-mcg-free-group-hosts-citation.md` (route)
- this note

The hole's own node was not edited.

## Referee (2026-09-16)

**Checked.**

- *Lemma A* (artifact Section 5), line by line, and the transfer formula (Lemma 2).
  The cycle structure of `σ_g` for central `g` and the cocycle identity are correct. So
  is the deduction `ψ^{mk} ∈ [D_0, D_0] ⇒ PF_{Λ^+}(ψ^m) = 0 ⇒ Λ^+ ∉ L(ψ^m) = L(ψ)`.
  No finiteness hypothesis on `D` is needed.
- *Lemma 1* against the BFH source. I extracted the arXiv v2 PDF independently of the
  solver and read:
  - Corollary 3.3.1, verbatim as quoted;
  - Lemma 3.1.13 and its proof, including "some iterate O^p is represented by an
    eg-aperiodic relative train track map" and "L(O^p) = L(O)";
  - Lemma 3.1.9;
  - Lemma 3.1.4, second part;
  - Definitions 3.1.5 and the lemma printed "Lemma 3.1.16. L(O) is O-invariant";
  - the Section 5.1 definition of PG/UPG;
  - the introduction's citation of Corollary 5.7.6.

  All match the artifact. The direction `ψ ∉ PG ⇒ L(ψ) ≠ ∅` is as the solver states. The
  naturality `θ_# L(ψ) = L(θψθ^{-1})` follows the Lemma 3.1.16 proof pattern correctly.
- *Lemma 4.* I recomputed the gluing (`χ = 2 − 2h − b`, `b` boundary components) and
  the nonseparation of `b_2, b_3, b_4, x, y, z` for all three lantern splittings. The
  abelianization argument is correct. The `h = 1` failure is correctly described
  (`MCG(S_{1,1})^{ab} ≅ Z`).
- *Theorem B, Corollary C (Lemma 5) and Theorem B′.*
  - The transfer from `C` to the normal core `N ≤ Γ` is correct.
  - The sign bookkeeping for `k < 0` is correct.
  - Lemma 5 uses only commuting `ψ_i` with `ψ_i^{±1}` in PG.
- *Korkmaz.* I fetched the arXiv e-print TeX of 1104.4816v2. Theorem 5
  (`thm:autF-n`) is quoted verbatim and the Section 6 proof is as described. The
  `g ≥ 3` input for `GL(n, C)` is Franks--Handel, arXiv:1102.4584 (abstract read).
- *Bridson--Vogtmann.* Question 16 of math/0507612 is "does every homomorphism from
  Aut(F_n) to Mod(S_g) have finite image", as the notes say. Korkmaz compares his
  Theorem 5 with it.
- *Duplicates and discipline.*
  - `bin/cairn search --similar` finds no duplicate. The nearest node is
    `rank-lower-bounds-for-free-group-hosts-of-out-fm-and-mcg`, which is handled by
    `distinct_from`.
  - Id lengths are 57 and 54.
  - Neither new claim is a hole.
- *Not verified.* Farb--Margalit numbering (Fact 3.7, Theorem 3.18, Proposition 5.1)
  could not be checked: the primer PDF was unreachable and the web-search budget was
  exhausted. The artifact flags these as recalled. The facts used (the conjugation
  formula for twists, the inclusion homomorphism, the lantern relation) are standard
  textbook facts.

**Changed.**

- The Korkmaz route now records the TeX-source recheck, the structure of the
  `g ≥ 3` proof, and that journal status was not rechecked.
- The claim marks Bridson's CAT(0) theorem as a recalled template that the proof
  does not use.
- The artifact (I4) records the numbering confirmation.

**Verdict.** Sound, and honestly labelled. Both direct routes are complete relative
to published or preprint sources whose statements I re-read. Novelty is not claimed,
and the novelty search remains incomplete. The hole
`some-closed-surface-mcg-embeds-in-no-out-free-group` remains OPEN: neither result
obstructs an embedding, as the solver says. Landed with small fixes.
