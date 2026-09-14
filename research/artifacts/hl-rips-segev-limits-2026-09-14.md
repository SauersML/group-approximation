# Lane hl-rips-segev-limits (2026-09-14)

**Target.** `rips-segev-groups-satisfy-kaplansky-zero-divisor` (Steenbock's
question), through `rips-segev-zero-divisor-via-special-marked-limits` and
`rips-segev-groups-are-marked-limits-of-special-groups`.

Nothing here is independently reviewed.

## 1. Verdict

**Partial. Steenbock's question stays OPEN.** Five findings:

1. **Classical theorems need a different kind of presentation.** Martin--Steenbock
   and Jankiewicz--Wise need a classical small cancellation presentation over the
   free product, with finitely many relators. The defining presentation of a
   Rips--Segev group is graphical: its relators are all the cycle labels of a
   finite graph, and they can share long subwords.
2. **Truncation doesn't help.** A quotient of `G` keeps those relators, so
   truncating the defining presentation doesn't give classical `C'(1/6)`
   approximants. A classical presentation of a quotient would have to be built
   differently, and none is known.
3. **The malnormal special quotient theorem is circular here.** It needs the
   ambient hyperbolic group to be virtually compact special already. Wise's
   statement was not pinned in this lane.
4. **Direct cubulation reduces to two open inputs.** Cubulating `G` through
   cubical small cancellation needs:
   - a `B(8)` wallspace on the single graph cone built from the Rips--Segev
     graph;
   - a properness and cocompactness theorem for `B(8)` presentations with graph
     cones and hyperbolic quotient.
5. **Landed elementary constraint.** In any `B(8)` wallspace on a graph cone
   whose edges are piece-paths, each wall class is an edge cut whose edges are
   pairwise at distance at least `9`.

## 2. Source pins

### 2.1 Steenbock, arXiv:1307.0981 (`main.tex`)

- l.120: "Do Rips-Segev groups satisfy Kaplansky's zero-divisor conjecture?"
- l.133: "the relators given by Rips-Segev can have long common parts"
- l.815--819: "Rips-Segev define a group by a graph with directed edges. Every
  edge of their graph is labeled by a word in $a^{\pm1},b^{\pm1}$. The letters
  $a$ and $b$ freely generate a free group $F:=\langle a \rangle *\langle
  b\rangle$. Let $R$ be the infinite set of elements in $F$ that are
  represented by the labels of all non-trivial cycles in their graph"
- l.1364, the `{a,b}`-reduction: "We replace the edge $(i,j)$ by a path $p$ of
  $P_i+Q_j+1$ edges in same orientation as $(i,j)$. [...] Finally, we reduce
  (or fold) the graph $\Phi'$ and obtain a reduced graph $\Phi''$ labeled by
  $\{a^{\pm1},b^{\pm1}\}$. The reduced graph $\Phi''$ is the
  $\{a,b\}$--reduction of $\Phi$."
- l.1407, Lemma `L: maxplength`: "Under the Rips-Segev condition, for all
  graphical pieces $p$ in $\Gamma$, we have that $\lvert \omega(p) \rvert_*
  \leqslant 3$."
- l.1414, Lemma `L: mincycle`: "Under the Rips-Segev condition, we have that $
  \gamma(\Gamma) \geqslant \girth (\Phi_{\Gamma}).$"
- l.1433, Corollary `C: final graphical small cancellation for Rips-Segev`: "A
  generalized Rips-Segev graph with coefficients $(I,O,C)$ satisfying the
  Rips-Segev condition and with underlying graph of girth $41$ satisfies the
  $Gr_*(1/8)$--condition."
- Section "Explicit constructions":
  - "The lemma gives a graph $\Phi$ with vertex degree $8$ and
    $\girth(\Phi)>41$."
  - "The original graphs used by Rips-Segev are such graphs $\Phi$."
- l.1562--1563:
  - "The coefficients used by Rips-Segev in their original construction satisfy
    our Rips-Segev condition, and the $\{a,b\}$--reduction of original
    Rips-Segev's $\Phi$ are generalized Rips-Segev graphs, denoted by
    $\Gamma_{\Phi}$."
  - "Rips-Segev's original groups coincide with the groups $G(\Gamma_{\Phi})$."
- l.1566, Theorem `T: RS are hyperbolic`: "Rips-Segev's original groups
  \cite{rips_torsion-free_1987} are non-elementary hyperbolic."

### 2.2 Martin--Steenbock, arXiv:1409.3678 (`RevCubFrProd3.tex`)

- l.268: "Let $\F$ be the free product of finitely many cubulable groups. If
  $G$ is a quotient of $\F$ by a finite set of relators which satisfies the
  classical $C'(1/6)$--small cancellation condition over $\F$, then $G$ is
  cubulable."
- l.329: "Let $X$ be $C'(1/6)$--small cancellation polygonal complex on which a
  group $G$ acts cocompactly, with cubulable vertex stabilisers and trivial
  edge stabilisers. Then $G$ is cubulable."
- l.307: "the generalised $B(6)$--condition \cite[Def. 5.1]{wise_structure_2011}
  is a key ingredient to construct an appropriate wallspace structure for the
  group in \cite[Th. 5.50]{wise_structure_2011}, and to obtain the properness
  of the action on the dual CAT(0) cube complex."
- l.309: "Indeed, properness is treated in Theorem 5.50 of
  \cite{wise_structure_2011}."
- l.317: "In Wise's Corollary 5.53 \cite{wise_structure_2011} (and in other
  related results as mentioned above), cocompactness of the action follows from
  the hyperbolicity of the quotient group."
- l.362--364: "It is unknown whether these so called generalised Rips-Segev
  groups satisfy the Kaplansky zero-divisor conjecture. It is therefore natural
  to ask, in light of Agol's theorem, whether our approach can be extended to
  cubulate some generalised Rips--Segev groups."
- `RevCubFrProd3.bbl` l.175--178: "\bibitem[Wis11]{wise_structure_2011} D.~T.
  Wise, \textsl{ The Structure of Groups with a Quasiconvex Hierarchy},
  \newblock (2011), \newblock available online (accessed 08/18/2014),"

### 2.3 Jankiewicz--Wise, *Cubulating small cancellation free products*

The PDF is dated "November 5, 2021". The text was extracted with pdftotext, and
tildes, primes, stars and fractions, garbled in the extraction, are restored.

- **Definition 2.1:** "A cubical presentation ⟨X | Y1, ..., Ym⟩ consists of a
  nonpositively curved cube complex X, and a set of local isometries Yi → X of
  nonpositively curved cube complexes. [...] As a topological space, X*
  consists of X with a cone on Yi attached to X for each i."
- **Definition 2.2:** "A cone-piece of X* in Yi is a component of Ỹi ∩ Ỹj, where
  Ỹi is a lift of Yi to the universal cover X̃*, excluding the case where i = j.
  A wall-piece of X* in Yi is a component of Ỹi ∩ N(Ũ), where Ũ is a hyperplane
  that is disjoint from Ỹi. For a constant α > 0, we say X* satisfies the C'(α)
  small-cancellation condition if diam(P) < α‖Yi‖ for every cone-piece or
  wall-piece involving Yi."
- **§2.3:** "We now describe a special case of the B(8) condition within the
  context of C'(α) metric small-cancellation. A piece-path in Y is a path in a
  piece of Y."
- **Definition 2.3:**
  - (1) "The collection of hyperplanes of each Yi are partitioned into classes
    such that no two hyperplanes in the same class cross or osculate, and the
    union U = ∪Uk of the hyperplanes in a class forms a wall in the sense that
    Yi − U is the disjoint union of a left and right halfspace."
  - (2) "If P is a path that is the concatenation of at most 8 piece-paths and
    P starts and ends on the carrier N(U) of a wall then P is path-homotopic
    into N(U)."
  - (3) "The wallspace structure is preserved by the group Aut(Yi → X) which
    consists of automorphisms φ : Yi → Yi such that [the triangle over X]
    commutes."
- **Theorem 2.4**, "from [FW21, Thm 3.5]": "Let X* = ⟨X | Y1, ..., Yk⟩ be a
  cubical presentation. Suppose X is compact, and each Yi is compact and
  deformation retracts to a closed combinatorial geodesic wi. Additionally,
  suppose that for every hyperplane U of Yi the complement Yi \ U is
  contractible, and U has an embedded carrier with diam N(U) < (1/20)‖Yi‖. If
  X* is C'(1/20) then X* is B(8) and π1X* acts properly and cocompactly on the
  CAT(0) cube complex dual to the wallspace on X̃*."
- **Lemma 2.7**, "[Wis21, Cor 5.30]": "Let X* be B(8). Suppose that pieces have
  uniformly bounded diameter. Then for each wall W, the map N(W) → X̃* is a
  quasi-isometric embedding with uniform quasi-isometry constants."
- **§3:** "The following is a simplified restatement of [HW14, Thm 7.12]".
  Theorem 3.1 is a relative cocompactness criterion for the dual cube complex.
  (That description is a summary, not a quote.)
- **Construction 4.3:**
  - "Let Tr be the union of directed edges e1, ..., er identified at their
    initial vertices. The long wedge of a collection of spaces X1, ..., Xr is
    obtained from Tr by gluing the basepoint of each Xj to the terminal vertex
    of ej."
  - "For each 1 ≤ k ≤ t let σk be a copy of e_{m(k)}^{-1} e_{m(k+1)} where
    m(t + 1) = m(1)."
- **Lemma 6.1:** "If ⟨G1, ..., Gr | R1, ..., Rs⟩ is C'_*(1/n) then for a
  sufficient subdivision of e1, ..., er the cubical presentation X* is C'(1/n)."
- **Theorem 6.2:** "Suppose G = ⟨G1, ..., Gr | R1, ..., Rs⟩ satisfies
  C'_*(1/20). If each Gi is the fundamental group of a [compact] nonpositively
  curved cube complex, then G acts properly [and compactly] on a CAT(0) cube
  complex." Its proof: "Theorem 2.4 asserts that π1X* acts freely (or with
  finite stabilizers if relators are proper powers) on a CAT(0) cube complex C
  dual to X̃*."
- **Bibliography:**
  - "[FW21] David Futer and Daniel T. Wise. Cubulating random quotients of
    hyperbolic cubulated groups, 2021."
  - "[HW14] G. C. Hruska and Daniel T. Wise. Finiteness properties of cubulated
    groups. Compos. Math., 150(3):453–506, 2014."
  - "[MS17] Alexandre Martin and Markus Steenbock. A combination theorem for
    cubulation in small cancellation theory over free products. Ann. Inst.
    Fourier (Grenoble), 67(4):1613–1670, 2017."
  - "[Wis21] Daniel T. Wise. The structure of groups with a quasiconvex
    hierarchy, volume 209 of Annals of Mathematics Studies. Princeton
    University Press, Princeton, NJ, 2021."

### 2.4 Search-result summaries (not read at source)

- **Einstein--Ng, arXiv:2111.03008:** relatively geometric actions for classical
  `C'(1/6)` quotients of free products.
- **Arzhantseva--Osajda, arXiv:1404.6807:** infinite graphical `C'(λ)`
  presentations with compatible walls give the Haagerup property.
- **Gruber--Martin--Steenbock, arXiv:1407.6850:** graphical small cancellation
  over free products and non-unique-product examples. The summary mentions no
  cubulation or Kaplansky results.

## 3. Analysis

### 3.1 Is a Rips--Segev group directly a classical `C'(1/6)` quotient?

**Not by any presentation known here.**

- **Factors.** `<a>` and `<b>` are infinite cyclic, hence cubulable and
  torsion-free hyperbolic. This hypothesis is harmless.
- **Relators.** The relators are all the cycle labels of a finite graph `Γ`.
  - Two cycles through a common path `p` have `ω(p)` as a common subword, which
    is a classical piece.
  - Steenbock records that the relators "can have long common parts" (l.133).
  - The graphical condition (l.1407) bounds only pieces coming from distinct
    immersions of paths with equal labels.
- **Finiteness.** `G` is hyperbolic, hence finitely presented, so some finite
  subset `R_0 ⊆ R` normally generates `<<R>>`.
  - Whether some such `R_0` satisfies classical `C'(1/6)` or `C'_*(1/20)` is
    unknown.
  - The obvious choices, fundamental cycles of a spanning tree, share tree
    paths. Nothing here controls the syllable length of those shared paths
    against the cycle lengths.
- **Truncations.** A quotient `G/<<S>>` is presented by `R ∪ S`, and adding
  relators never removes the pieces inside `R`. So the ball-injective classical
  quotients asked for in the directive would need an unrelated presentation of
  the quotient. No construction is known.

### 3.2 Malnormal special quotient theorem

It needs the ambient hyperbolic group to be virtually compact special, which is
what is being sought, so it is circular here. Wise's statement was not pinned in
this lane.

### 3.3 Direct cubical small cancellation

- **Setup.** For the one graph cone `Y` built from `Γ` (the graph analogue of
  Construction 4.3), `π_1 <X | Y> = G`. Theorem 2.4 covers only circle cones.
- **Input 1: `C'(1/20)` for `Y`.** Expected from Steenbock's piece and cycle
  bounds plus the subdivision estimate of Lemma 6.1. Not written out.
- **Input 2: a `B(8)` wallspace on `Y`.** Open.
- **Then properness and cocompactness** need a `B(8)` theorem for graph cones
  with hyperbolic quotient. Martin--Steenbock point to Wise, Theorem 5.50 and
  Corollary 5.53, which were not read here.
- **Necessary shape of the walls** (landed, elementary): each class is an edge
  cut, no two class edges share a vertex, and endpoints of distinct class edges
  are at distance at least `9`.
- **Definitional caveat.** Definition 2.2 as printed excludes `i = j` for
  cone-pieces, so a single-cone presentation would have no cone-pieces. The
  application needs the reading in which distinct lifts of one cone give
  cone-pieces.

## 4. Nodes from this lane

- `b8-graph-cone-wall-classes-are-sparse-edge-cuts`: ESTABLISHED, elementary,
  landed-unreviewed. Proof route: `b8-graph-cone-wall-classes-sparse-cuts-proof`.
- `rips-segev-graph-cones-admit-b8-wallspaces`: OPEN.
- `b8-hyperbolic-cubical-presentations-cocompactly-cubulated`: OPEN import.
- `rips-segev-cubulation-via-b8-graph-cone-wallspaces`: route to
  `rips-segev-groups-are-cocompactly-cubulated`.
- An Attempts section on `rips-segev-groups-are-marked-limits-of-special-groups`.

## 5. Exact gap

1. **Walls.** A `B(8)` wallspace on the graph cone `Y` of a large-girth
   Rips--Segev graph. Its classes must be sparse edge cuts, satisfy condition
   (2) for concatenations of up to `8` piece-paths, and be
   `Aut(Y -> X)`-invariant.
2. **Import.** A verbatim-pinned theorem: `C'(1/20)` + `B(8)` + graph cones +
   hyperbolic `π_1 X*` gives a proper cocompact action. The candidates are Wise,
   Theorem 5.50 and Corollary 5.53.
3. **Alternative, for approximants.** A quotient of `G`, injective on the ball of
   radius `R`, with some finite classical `C'(1/6)` presentation over a free
   product of cubulable torsion-free hyperbolic groups. No construction is known.

## 6. Not done

- **Cairn `why` on MSI.** The MSI control master was down: `ssh -O check`
  reported no control socket. Only a local lint ran: titles present, and
  referenced ids exist on main or in this commit.
- **Wise 2021, Chapter 5:** not read.
