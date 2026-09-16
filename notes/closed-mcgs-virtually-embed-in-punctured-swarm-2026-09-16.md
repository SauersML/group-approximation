# closed-mcgs-virtually-embed-in-punctured-mcgs: swarm attack, 2026-09-16

Lane: `swarm-closed-mcgs-virtually-embed-in`. Target hole:
`closed-mcgs-virtually-embed-in-punctured-mcgs`. For `g ≥ 3`, does some
finite-index `L ≤ Mod(S_g)` embed in the extended mapping class group of a
finite-type surface with at least one puncture or boundary component? It feeds
`closed-mcg-bh-via-punctured-mcg-host` and
`closed-mcg-aut-embedding-via-punctured-host`.

**Outcome in one line.** The hole stays open. Every solution has one of two
shapes, (A) or (B) below.
- Shape (A) is excluded whenever its closed copy is, up to conjugation, a
  covering lift, and in particular in the same genus.
- Hosts of genus `≤ 1` would force a finite-index subgroup of `Mod(S_g)` with
  infinite abelianization. That is a counterexample to the conjecture recorded
  by Putman--Wieland, so these hosts are excluded wherever that conjecture holds.
- Shape (B) with host genus `≥ 2` is untouched in nodes. No contradiction was
  found there. The notes-only sketches 3.5 and 3.7 narrow it: a finitely
  generated kernel gives `L′ ↪ Aut(K)`, and if it also has infinite index in the
  point-pushing group, the quotient image is reducible.

## 0. Setup and conventions

- `S_{h,m}`: closed genus-`h` surface minus `m` points. `PMod(S_{h,m})`:
  orientation-preserving classes fixing each puncture. `Mod(S_h, *)` =
  `PMod(S_{h,1})`. `p`: forgetful maps.
- **Birman exact sequence** (Farb--Margalit primer, Thm 4.6; not re-read
  here). If `χ(S_{h,j}) < 0`, then
  `1 → π_1(S_{h,j}) → PMod(S_{h,j+1}) → PMod(S_{h,j}) → 1`, where the kernel is
  the point-pushing subgroup.
- **Virtual cohomological dimension** (Harer, Invent. Math. 84 (1986); cited
  as in `rank-lower-bounds-for-free-group-hosts-of-out-fm-and-mcg-proof`,
  theorem numbers not re-read). `vcd Mod(S_g) = 4g − 5` for `g ≥ 2`.
- **Trivial centre.** A finite-index subgroup of `Mod(S_g)`, `g ≥ 3`, has
  trivial centre. Argument: a central `z` commutes with some power of every
  Dehn twist, so it fixes every curve and is trivial for `g ≥ 3`. This is the
  Farb--Margalit argument for `Z(Mod(S_g)) = 1`, not re-read.

## 1. Literature gate (dated)

**Tooling on 2026-09-16.**
- The web-search budget ran out partway through.
- The arXiv export API first returned "Rate exceeded" and then "Connection
  reset by peer".
- Fetching arxiv.org/abs pages directly still worked, and PDFs were extracted
  locally.
- So the gate is thinner than intended. Every item below is marked with what was
  actually seen.

**Read and used in nodes.**
- **J. Behrstock, D. Margalit**, *Curve complexes and finite index subgroups of
  mapping class groups*, arXiv:math/0504328v2. Title page and Section 1 read
  from the PDF on 2026-09-16.
  - Theorem 3 is quoted verbatim in
    `closed-mcg-finite-index-injections-citation`. So is their credit to Irmak
    for every `S_{g,n}` with `g ≥ 2` other than `S_{2,0}`.
  - Irmak, Topology 43(3) (2004) 513--541 (arXiv:math.GT/0211139 and
    math.GT/0407285) is known only through that attribution and was not read.
- **A. Putman, B. Wieland**, *Abelian quotients of subgroups of the mapping
  class group and higher Prym representations*, arXiv:1106.2747. Abstract only,
  2026-09-16. The conjecture it records ("does not virtually surject onto Z if
  the genus of the surface is large") is quoted in
  `closed-mcg-low-genus-host-gives-infinite-abelianization`.
- **H. Baik, S.-H. Kim, T. Koberda**, *Unsmoothable group actions on compact
  one-manifolds*, arXiv:1601.05490v4 (10 Jun 2016). Introduction read from the
  PDF on 2026-09-16.
  - It states Question 1: does `Mod(S)`, genus `≥ 2`, virtually admit a
    faithful `C^1` action on a compact one-manifold?
  - It also says: "Ivanov conjectured that every finite index subgroup of a
    higher genus mapping class group has finite abelianization [20]", and that
    Parwani's Conjecture 1.6 notes this anticipates a negative answer to
    Question 1 when the genus is at least four. The text extraction garbled some
    symbols, and the quotation was checked against the extracted text.

**Imported through existing repo nodes (not re-read this session).**
- Chen--Salter, arXiv:1804.11235v1, Theorem A, via
  `birman-exact-sequence-does-not-virtually-split` (read there 2026-09-12).
- Luo--Watanabe, arXiv:2502.14343v2, Theorem 1, via the target's artifact
  `research/artifacts/bh-out-fn-closed-mcg-2026-09-12.md`.
- Aramayona--Souto, arXiv:1011.1855v1, and Aramayona--Leininger--Souto,
  arXiv:0811.0841v1, abstracts, via the target node's Attempts 2 and 3.
- The based Dehn--Nielsen--Baer theorem, via
  `based-dehn-nielsen-baer-for-closed-surfaces`.

**Titles, links or abstracts only (2026-09-16). Paper bodies were not read.**
- K. Mann, M. Wolff, *Rigidity of mapping class group actions on S^1*,
  arXiv:1808.02979.
- *C^1 actions on the circle of finite index subgroups of Mod(Σ_g), Aut(F_n),
  and Out(F_n)*, arXiv:2108.06814v3. Authors were not recorded.
- *Exotic mapping class group actions on the circle*, arXiv:1603.02098. Whether
  it has been withdrawn was not verified.
- S. Bigelow, R. Budney, *The mapping class group of a genus two surface is
  linear*, arXiv:math/0010310, Algebr. Geom. Topol. 1 (2001) 699--708. The
  abstract was fetched on 2026-09-16 and says: "We obtain a faithful
  representation of the mapping class group of the n-punctured sphere by using
  the close relationship between this group and B_{n-1}." This is used only in
  a remark in section 3 below.

**Standard sources not re-read.** Farb--Margalit, *A Primer on Mapping Class
Groups* (Birman exact sequence Thm 4.6, capping Prop. 3.19, centre, `SL_2(Z)`);
Harer (vcd); Serre (vcd independent of the subgroup); Nielsen--Schreier.

**Not verified.**
- The current status of the Ivanov / Putman--Wieland conjecture. Partial results
  I remember include McCarthy and Hain for subgroups containing the Torelli
  group, Putman for level subgroups, Ershov--He, and Landesman--Litt. Their
  exact statements and scopes were not checked.
- Clay--Mangahas--Margalit (free normal subgroups of mapping class groups).
- Dahmani--Guirardel--Osin, as far as it concerns free normal subgroups of
  `Mod`.

**No source found for the target itself.** Nothing located either constructs a
finite-index subgroup of a closed-surface mapping class group, `g ≥ 3`, inside
a punctured or bordered mapping class group, or rules it out. The search is
thin, see the tooling note above.

## 2. What was proved

Four claims, each with one route. Throughout, `g ≥ 3`, `L ≤ Mod(S_g)` has
finite index, and `ι: L → Mod^±(Σ′)` is injective, where `Σ′` has genus `h`,
`n` punctures, `b` boundary components and `m = n + b ≥ 1`.

**(R) Rigidity import.** `closed-mcg-finite-index-injections-are-conjugations`,
route `closed-mcg-finite-index-injections-citation`.
- **Statement.** Every injection of a finite-index subgroup of `Mod^±(S_g)`
  into `Mod^±(S_g)` is conjugation by some `φ ∈ Mod^±(S_g)`.
- **Source.** Behrstock--Margalit Theorem 3, which credits the closed case to
  Irmak.
- The node carries the verbatim theorem and conventions, and the genus-2
  exception.

**(D) The forgetful dichotomy.** `closed-mcg-punctured-host-forgetful-dichotomy`,
route `closed-mcg-punctured-host-forgetful-dichotomy-proof` (direct).
1. **Normal form.**
   - Pass to pure orientation-preserving classes.
   - If the boundary is fixed pointwise, cap it. The kernel of each capping is a
     central boundary twist. The copy of `L` has trivial centre (Step 1, the
     twist-power argument), so it meets that kernel trivially.
   - The result is `ρ′: L′ ↪ PMod(S_{h,m})`.
2. **Forgetful tower.** Forget punctures one at a time, `ρ′_j`, `j = m, …, 0`.
3. **Shape A: `ρ′_0` injective.**
   - `h ≥ g`, by vcd `4h − 5 ≥ 4g − 5`.
   - `ρ′_1` splits the Birman sequence of `S_h` over `ρ′_0(L′)`.
   - Conversely, such a split copy is already a punctured host.
4. **Shape B: `ρ′_0` not injective.** Let `j` be the last non-injective index.
   - `χ(S_{h,j}) < 0`.
   - `K = ker ρ′_j` is nontrivial and normal.
   - `K` embeds in the point-pushing subgroup, so it is free (`j ≥ 1`) or a
     surface subgroup (`j = 0`).
   - `K` is infinite and not cyclic, since a normal `Z` would give a central
     element of an index-≤2 subgroup.
   - `L′/K ≅ ρ′_j(L′) ≤ PMod(S_{h,j})`.

**(N) No marked lift of covering-lift copies.**
`covering-lift-copies-of-closed-mcgs-have-no-marked-lift`, route
`covering-lift-copies-no-marked-lift-proof`.
- **Statement (a).** For a finite unbranched cover `π: Σ̃ → Σ = S_g` and
  `∗ ∈ Σ̃`, no homomorphism `ρ_1: L → Mod(Σ̃, ∗)` has every forgotten class
  `p(ρ_1(f))` with a covering representative.
- **Relation to earlier nodes.** The existing no-go nodes assumed covering
  representatives rel the marked points. Here only the forgotten class is
  assumed to cover.
- **Idea of the proof.**
  - Correct the covering representative `F` of `p(ρ_1(f))` along the track
    `γ` of an isotopy from a based representative `R_f` to `F`. This gives
    `[R_f∘α] = [γ·(F∘α)·γ̄]`.
  - Push down to `β_f := [δ·(f′∘·)·δ̄] ∈ Aut(π_1(Σ, x))`, with `δ = π∘γ`.
  - `β_f` preserves `H = π_*π_1(Σ̃, ∗)`, restricts to the homomorphism
    `λ(f) = π_* R_{f*} π_*^{-1}`, and represents `f` in `Out`.
  - Form (i) of `outer-covering-lifts-are-virtual-sections` makes
    `f ↦ β_f` a homomorphism. Based DNB turns it into a virtual section of the
    Birman sequence.
  - That contradicts Chen--Salter for `g ≥ 4`, and the unreviewed genus-3 node
    for `g = 3`.
- **Statement (b), same genus.** By (R), `ρ_0 = c_φ` is a covering lift of
  degree one for `π = Φ^{-1}`. So no injective `ρ_0: L → Mod(S_g)` lifts to
  `Mod(S_g, ∗)`.
- **For (D).** Shape A is impossible with `h = g`, or with `ρ′_0` a covering
  lift up to conjugation.

**(G) Low-genus hosts.** `closed-mcg-low-genus-host-gives-infinite-abelianization`,
route `closed-mcg-low-genus-host-abelianization-proof`.
- **Statements.**
  - If `h = 0`, every nontrivial subgroup of `L′` surjects onto `Z`. So `L′`
    surjects onto `Z` and is torsion-free.
  - If `h = 1`, every infinite subgroup of `L′` virtually surjects onto `Z`.
  - So a host of genus `≤ 1` gives a finite-index subgroup of `Mod(S_g)` with
    infinite abelianization.
- **Proof.** Take the first index `i` at which the image of the subgroup is
  nontrivial. The image lies in the free group `π_1(S_{h,i−1})`. For `h = 1`,
  first intersect with a free finite-index subgroup of `SL_2(Z) = PMod(S_{1,1})`
  or with `ker ρ′_1`.
- **Relation to Aramayona--Souto.** Attempt 2 of the target uses
  Aramayona--Souto for the full group with target genus `≤ 2g − 1`. (G) covers
  finite-index subgroups, but only for target genus `≤ 1`, and only modulo the
  Ivanov / Putman--Wieland conjecture.

**Derived facts recorded in the nodes.**
- (N)(a) implies both existing covering-lift no-go claims.
- The dichotomy's converse shows that shape A alone would prove the target.

## 3. Approaches and exactly where each dies

Items 3.1--3.4 are proved in nodes. Items 3.5--3.12 are sketches or dead ends
recorded only here. They use inputs that were not re-read, and none of them is a
node.

**3.1 Forget all punctures (shape A) and invoke Chen--Salter.** *Partly works.*
- Shape A splits the Birman sequence of `S_h` over `Γ := ρ′_0(L′)`.
- Chen--Salter exclude splittings over finite-index subgroups of `Mod(S_h)` and
  over finite-index subgroups of Torelli. Luo--Watanabe exclude them over
  subgroups containing the Johnson subgroup.
- *Dies* for `h > g`. By vcd `Γ` has infinite index in `Mod(S_h)`, and it is
  isomorphic to a finite-index subgroup of `Mod(S_g)`. None of those
  non-splitting theorems addresses such a `Γ`. For `h = g`, (R) makes `Γ` of
  finite index, and (N)(b) excludes it.

**3.2 Push a marked lift down along a cover (N).** *Works* when `ρ′_0` is a
covering lift up to conjugation.
- *Dies* for a non-covering `ρ′_0`. Without a covering representative there is
  no `β_f` on `π_1(S_g)` restricting to the marked automorphism of the cover.
- Aramayona--Leininger--Souto build injections between mapping class groups of
  different closed surfaces. Whether they are covering lifts in the sense of (N)
  was not examined, so their marked-lift question is still open.

**3.3 Low-genus hosts (G).** *Works modulo a conjecture.*
- *Dies* as an unconditional exclusion. That would need
  `H_1(L″; Q) = 0` for every finite-index `L″ ≤ Mod(S_g)`, which is the Ivanov /
  Putman--Wieland conjecture. Its status was not verified.

**3.4 Commuting-centre arguments in shape B.** *Works* to show that `K` is not
cyclic (Step 6.4 of the dichotomy proof).
- *Dies* for larger `K`. A free or surface group `K` of rank `≥ 2` has trivial
  centre, and no abelian normal subgroup is forced.

**3.5 `K` is free and finitely generated.**
- Conjugation gives `L′ → Aut(K)`. Its kernel `C := C_(L′)(K)` is normal and
  `C ∩ K = Z(K) = 1`, so `C` and `K` are commuting normal subgroups.
- *Sketch.* Assume two standard inputs:
  - Ivanov's trichotomy: an infinite irreducible subgroup contains a
    pseudo-Anosov;
  - McCarthy: the centralizer of a pseudo-Anosov is virtually cyclic.

  Then a finite-index subgroup of `Mod(S_g)`, `g ≥ 3`, has no two nontrivial
  commuting normal subgroups:
  - a nontrivial normal subgroup is infinite, since a finite one would
    centralize a finite-index subgroup;
  - it is irreducible, since its canonical reduction system is invariant;
  - so it contains a pseudo-Anosov, whose centralizer is virtually cyclic;
  - an infinite virtually cyclic normal subgroup contains a characteristic `Z`,
    which contradicts Step 6.4.
- So `C = 1` and `L′ ↪ Aut(F_r)`.
- *Dies* there: whether finite-index subgroups of `Mod(S_g)` embed in `Aut(F_r)`
  is exactly the downstream open question `closed-mcg-aut-embedding-via-punctured-host`.
  Nothing contradicts it.

**3.6 `K` is free or surface, finitely generated, of finite index in the
point-pushing group.**
- Then `ρ′_(j+1)(L′)` preserves a finite-index subgroup of `π_1(S_(h,j))`. So
  `L′` acts on the corresponding finite cover, and `L′ ↪ Aut(K)` gives a based
  mapping class group of that cover.
- *Dies* as circular: it is a new host of larger complexity, not a
  contradiction.
- For `j = 0` it would make `L′` a closed-surface-by-(subgroup of `Mod`) group
  with a normal closed surface subgroup. No obstruction to that was found.

**3.7 `K` finitely generated, of infinite index in the point-pushing group
`π := π_1(S_(h,j))`, any `j`.**
- *Sketch, not checked.* Write `P := Push(π) = ker p`. Suppose `ρ′_j(L′)`
  contains a pseudo-Anosov `ψ`. Pick `x ∈ L′` over `ψ` and put
  `φ := ρ′_(j+1)(x)`.
  - `p^-1(<ψ>) = P ⋊ <φ>` is `π_1` of the mapping torus `M_ψ`. It is a finite
    volume hyperbolic 3-manifold by Thurston, since `χ(S_(h,j)) < 0` (Step 6.1).
  - `φ` normalizes `ρ′_(j+1)(K) ≤ P`, since `K` is normal in `L′`.
- **`K` is geometrically finite.** Otherwise tameness and Canary's covering
  theorem give a finite cover `M′ → M_ψ` fibring over the circle, and a finite
  index `K_0 ≤ K` that is normal in `π_1(M′)` with quotient `Z`.
  - `π′ := P ∩ π_1(M′)` is also normal in `π_1(M′)` with quotient `Z`, and
    `K_0 ≤ π′`.
  - A subgroup of `Z` with quotient `Z` is trivial, so `K_0 = π′`, which has
    finite index in `P`. That contradicts the infinite index of `K`.
- **Stabilizer.** `K` is torsion-free, not cyclic (Step 6.4) and f.g. in a
  surface group, so it is non-elementary. Put `H := Stab(Λ(K))` in `π_1(M_ψ)`.
  - `Λ(H) = Λ(K)`, so `H^3/K → H^3/H` restricts to a covering of the
    1-neighbourhoods of the convex cores, of degree `[H : K]`.
  - The first has finite positive volume by geometric finiteness, so
    `[H : K] < ∞`.
- **Contradiction.** `φ` normalizes `K`, so `φ ∈ H` and `φ^n ∈ K ≤ P` for some
  `n ≥ 1`. But `p(φ^n) = ψ^n ≠ 1`.
- So `ρ′_j(L′)` contains no pseudo-Anosov.
  - It is infinite: otherwise `K` has finite index in `L′`, and
    `vcd K ≤ 2 < 4g − 5`.
  - By Ivanov's trichotomy it is reducible.
- *Dies* there. A reducible image of the quotient `L′/K` gives no embedding of
  `L′` itself. A finite-index `L‴ ≤ L′` fixing the reduction system only gives
  an embedding of `L‴/N` in a product of mapping class groups of the
  complementary components. Here `N ⊇ K ∩ L‴` is normal in `L‴` and
  `N/(K ∩ L‴)` is abelian (the twist part).
- None of the inputs was re-read:
  - hyperbolization of mapping tori of pseudo-Anosovs of punctured surfaces;
  - tameness and Canary's covering theorem in the cusped case;
  - the convex-core volume argument;
  - the equivariance `φ Push(γ) φ^-1 = Push(φ_*(γ))`.

**3.8 `K` not finitely generated.**
- *Dies* outright. Dahmani--Guirardel--Osin rotating families (not re-read) give
  infinitely generated free normal subgroups of `Mod(S_g)` all of whose
  nontrivial elements are pseudo-Anosov.
- So "normal, free, no `Z^2`" is not contradictory by itself. In such a `K`,
  every commutator `[T_c^N, k]` is pseudo-Anosov, so the disjoint-translate
  trick for building a `Z^2` inside `K` fails.

**3.9 Convex cocompactness.**
- *Sketch.* A finitely generated, purely pseudo-Anosov, convex cocompact `K`
  would have finite index in its normalizer, via the proper action on the weak
  hull of its limit set in Teichmüller space (Farb--Mosher, not re-read). That
  contradicts `vcd L′ = 4g − 5 > 2`.
- *Dies*:
  - `K` need not be purely pseudo-Anosov;
  - convex cocompactness of finitely generated purely pseudo-Anosov free
    subgroups is not known in general, as far as I know (unverified).

**3.10 Reducible closed copies.**
- *Sketch, not a node.* Suppose `Γ = ρ′_0(L′) ≤ Mod(S_h)` virtually fixes a
  nonempty multicurve `C`.
  1. Cutting along `C` has an abelian twist kernel (Farb--Margalit Prop. 3.20,
     not re-read). It meets the copy trivially, because normal abelian subgroups
     are trivial by the argument of 3.5.
  2. So a finite-index subgroup embeds in `∏_i PMod(R_i)`, where the `R_i` are
     the punctured components of `S_h − C`, each of genus `≤ h − 1`.
  3. If no projection were injective, two kernels would be commuting nontrivial
     normal subgroups, which 3.5 excludes. Inducting on the number of factors,
     some single projection is injective.
- So a reducible closed copy gives a punctured host of smaller genus.
- *Use.* A minimal-genus shape-A host has irreducible `ρ′_0`. This is a
  normalisation, not an exclusion.

**3.11 Circle actions and orderability.**
- A host should make `L′` act faithfully on `S^1`, by a Nielsen-type action at
  infinity based at one puncture.
  - BKK's Theorem 1.1 records the classical case. In their notation `S_{g,n,b}`
    has `n` marked points and `b` boundary components, and the case is
    `S_{g,1,0}`.
  - Extending it to several punctures and to boundary components is standard,
    but was not re-read.
- *Dies*: the `C^0` question for finite-index subgroups of `Mod(S_g)` is not
  settled by anything found. BKK's Question 1 asks the `C^1` version, and Mann--Wolff
  was seen only as a title.

**3.12 Linearity for genus-0 hosts.**
- A genus-0 host makes `L′` linear, through Bigelow--Budney's faithful
  representation of punctured-sphere mapping class groups. It also makes `L′`
  torsion-free and locally indicable, by (G).
- *Dies*: as far as I know linearity of `Mod(S_g)`, `g ≥ 3`, is open (status
  not verified this session), so no contradiction follows. (G) is the sharper
  genus-0 consequence recorded.

## 4. What remains open

**The target is still OPEN.** By (D), (N) and (G), a host must be one of the
following.
1. **Shape A with `h > g`.**
   - `ρ′_0: L′ ↪ Mod(S_h)` is not a covering lift up to conjugation.
   - It lifts to `Mod(S_h, ∗)`.
   - By 3.10 it may be taken irreducible after lowering the genus. That step is
     a sketch.
2. **Shape B with `h ≥ 2`**, or with `h ≤ 1` for a `g` at which `Mod(S_g)`
   virtually surjects onto `Z`.
   - There is a nontrivial, non-cyclic, free or surface-subgroup normal kernel
     `K`.
   - `K` is either infinitely generated, or finitely generated with
     `L′ ↪ Aut(K)`. The latter uses the sketch in 3.5.
   - If `K` is finitely generated of infinite index in the point-pushing group,
     then `ρ′_j(L′)` is infinite and reducible. That uses the sketch in 3.7.

**Concrete sub-questions a next attempt could take.**
- **(Q1)** For `g ≥ 3` and `h > g`, is every injective homomorphism from a
  finite-index subgroup of `Mod(S_g)` to `Mod(S_h)` a covering lift up to
  conjugation? A yes, with (N), kills shape A. Aramayona--Souto cover the full
  group, `g ≥ 6`, `h ≤ 2g − 1`. Finite-index subgroups and larger `h` were not
  found in the literature.
- **(Q2)** Can a finite-index subgroup of `Mod(S_g)`, `g ≥ 3`, contain a nontrivial
  normal subgroup that is isomorphic to a subgroup of a surface group? A no kills
  shape B completely. A yes via DGO still has to meet the point-pushing
  constraint `ρ′_(j+1)(K) = ρ′_(j+1)(L′) ∩ Push`.
- **(Q3)** Write 3.5 (no two commuting nontrivial normal subgroups) and 3.10
  (reducible copies lower the genus) as nodes, with Ivanov's trichotomy and
  McCarthy's centralizer theorem imported by verbatim citation.
- **(Q4)** Verify the current status of the Ivanov / Putman--Wieland conjecture
  in some genus `≥ 3`. Any proved case turns (G) into an unconditional exclusion
  of hosts of genus `≤ 1` in that genus. By Putman--Wieland's abstract, the
  conclusion then passes to all larger genera.

**Review targets.**
- The genus-3 case of (N) depends on
  `birman-sequence-genus-three-does-not-virtually-split`, which is unreviewed.
- Step 3 of the dichotomy proof caps boundary with central kernels. The capping
  statement (Farb--Margalit Prop. 3.19) and its small-surface hypotheses were not
  re-read.
- Step 5 of the (N) proof identifies the point-pushing subgroup with `Inn(G)`
  under based DNB. This is standard, but it is asserted without citation there.

**Files.**
- Nodes:
  - `research/closed-mcg-finite-index-injections-are-conjugations.md`
  - `research/closed-mcg-finite-index-injections-citation.md`
  - `research/closed-mcg-punctured-host-forgetful-dichotomy.md`
  - `research/closed-mcg-punctured-host-forgetful-dichotomy-proof.md`
  - `research/covering-lift-copies-of-closed-mcgs-have-no-marked-lift.md`
  - `research/covering-lift-copies-no-marked-lift-proof.md`
  - `research/closed-mcg-low-genus-host-gives-infinite-abelianization.md`
  - `research/closed-mcg-low-genus-host-abelianization-proof.md`
- No experiments or artifacts.
