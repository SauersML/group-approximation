# every-hyperbolic-group-is-good — swarm lane, 2026-09-16

Target: `every-hyperbolic-group-is-good`, which says every word-hyperbolic group is good
in Serre's sense. Lock `every-hyperbolic-group-is-good` was held for this lane. Outcome:
an **exact reduction**. The target is proved equivalent to Gromov's question plus a new
cohomological hole in degrees `>= 3`. Neither is decided.

Full proofs: `research/artifacts/hyperbolic-goodness-rf-plus-high-degree-reduction-2026-09-16.md`.

## Setup

- *Good*: `inf: H^q(G_hat;M) -> H^q(G;M)` is an isomorphism for all `q` and all finite
  `G`-modules `M`.
- *Effaceable class*: one that restricts to zero on some finite-index subgroup.
- `(E_n)`: all classes in degrees `1..n` are effaceable.
- `(A_n)`: inflation is bijective in degrees `0..n`.

Graph state at the start:

- `every-hyperbolic-group-is-good` was open. Its Attempts record that special cube
  complexes stop at Kazhdan groups.
- `good-groups-have-no-persistent-finite-cohomology` (good implies effaceable) was
  established.
- `good-cocompact-proper-groups-are-virtually-torsion-free` (universal goodness implies
  universal vtf, hence universal RF) was established.
- `universal-hyperbolic-vtf-iff-rf` (Wise) was established.
- `hyperbolic-finite-residual-is-torsion-free` (Gromov's question, positive form) was
  open.

## What was proved (all in the artifact)

1. **Proposition 1: `(E_n) => (A_n)` for every group.** This is Serre's exercise I.2.6,
   proved here by induction with the coinduced module `Map(G/U,M)` and a ladder chase.
   Graph: claim `effaceable-cohomology-makes-inflation-an-isomorphism`, direct proof
   `effaceable-cohomology-makes-inflation-an-isomorphism-proof`.
2. **Degrees one and two.**
   - `(E_1)` holds for every group.
   - A degree-two class whose extension is residually finite is effaceable.
   - For residually finite `G`, `(E_2)` is equivalent to residual finiteness of all
     finite-module extensions.
3. **Finite index and coefficients.**
   - Effaceability ascends to finite-index overgroups.
   - For a class of groups closed under finite-index subgroups, effacement with trivial
     `F_p` coefficients gives effacement with all finite coefficients (induction on
     `|M|`).
4. **Theorem 4.** Every hyperbolic group is good iff both of the following hold:
   - (a) every hyperbolic group is RF;
   - (b) on every torsion-free hyperbolic group, every class in `H^q(-;F_p)` with
     `q >= 3` is effaceable.

   The direction `2 => 1` is route `every-hyperbolic-group-good-via-rf-and-high-degrees`.
   The direction `1 => 2` uses existing established nodes and is recorded only in prose,
   to avoid a pointless equivalence cycle. (b) is the new hole
   `torsion-free-hyperbolic-mod-p-classes-die-virtually`.
5. **vcd `<= 2`.** Under (a), every hyperbolic group of vcd `<= 2` is good.
   Unconditionally, for such an RF `G` with torsion-free finite-index `H`:
   `G` is good iff every finite-module extension of `H` is RF. For `GHB_2(7)`,
   `ker ψ` acts freely and cocompactly on the 2-complex `Y`, so `cd <= 2`. So `GHB_2(7)`
   is good and RF iff all finite-module extensions of `ker ψ` are RF.
6. **Lemma 6.** A residually finite central extension by `Z/n` has its class inflated
   from a finite quotient. Hence (a) alone gives
   `ghb7-finite-index-subgroup-has-degree-two-inflation-surjectivity` (route
   `ghb7-degree-two-inflation-via-universal-rf`). The existing route needed universal
   goodness.

   A shorter observation, not put in the graph: under (a), for a central `Z`-extension
   `K~` of a hyperbolic `K`, the quotient `K~/<z^n>` is hyperbolic and RF, so `z` has order
   exactly `n` in a finite quotient. This gives the centre-survival conclusion directly.

## Approaches to (b) and where each dies

- **Special cube complexes / Kropholler–Wilkes.** These handle hyperbolic virtually
  compact special groups. They die at non-cubulated groups, in particular Kazhdan groups.
- **Ideal of effaceable classes.** The effaceable classes form a two-sided ideal
  containing `H^1` and `H^2` under (a). So it suffices to efface degree-`>=3`
  indecomposables. *Dies*: indecomposables exist, e.g. the top class of a hyperbolic
  3-manifold with `H_1(M;F_p) = 0`.
- **Pullbacks from good or low-dimensional groups.** Maps from Kazhdan groups to
  cubulated groups have finite image (fixed points, recalled), so the pulled-back classes
  are trivially effaced. No construction of maps to small-vcd hyperbolic targets that are
  nonzero in degree `> vcd` is known.
- **Top degree of `PD^n` groups.** Restriction is multiplication by the index. Under (a),
  Dehn filling gives quotients of order divisible by `p`, so the top class is effaceable.
  *Dies*: only the top degree is reached.
- **Test case, not computed.** Torsion-free cocompact lattices in `Sp(n,1)` and
  `F_4^(-20)` are hyperbolic, Kazhdan and linear (so RF), with cd `>= 8`. For them
  goodness is (b) on the lattice and its finite-index subgroups *plus* residual finiteness
  of all finite-module extensions (referee correction: RF of the lattice alone does not
  give the degree-two half). No source was found either way. A persistent class there would refute the
  target without touching Gromov's question.
- **Direct attack on the target.** It is at least as hard as Gromov's question, which is
  open (Cui–Wan arXiv:2604.04007, via the graph). So no proof was attempted; the
  reduction isolates what goodness adds.

## Literature (dates of checking)

- Grunewald, Jaikin-Zapirain, Zalesskii, Duke Math. J. 144 (2008) 53–72,
  DOI 10.1215/00127094-2008-031. Abstract fetched 2026-09-16 (Project Euclid; the first
  URL attempt with a wrong DOI prefix returned 404).
- Kropholler–Wilkes, arXiv:1603.07197, Thm 9. Via `good-groups-have-no-persistent-finite-cohomology`,
  checked there 2026-08-30.
- S. Hughes, A. Ng, arXiv:2601.05706 (9 Jan 2026). Fetched 2026-09-16. It lists virtually
  compact special groups as good and says nothing about all hyperbolic groups.
- M. Boggi, P. Zalesskii, arXiv:2406.08639 (v1 12 Jun 2024, v2 28 Oct 2024). Abstract
  fetched 2026-09-16. No claim about all hyperbolic groups.
- arXiv:2603.04197 (4 Mar 2026) was seen in search results and is irrelevant.
- Cui–Wan arXiv:2604.04007 (5 Apr 2026). Gromov's question is still called open there
  (via the graph node, checked 2026-09-07).
- Wise, *Complete square complexes*, CMH 82 (2007). Via `universal-hyperbolic-vtf-iff-rf`.
- Serre, *Galois Cohomology* I.2.6 Ex. 1–2; Brown, *Cohomology of Groups* III.5–6, IV.3.
  Recalled, **not fetched**.
- Bridson arXiv:1907.08072. The PDF fetch returned binary and there was no extractor, so
  it was **not read** and is not cited in the graph.
- Web searches 2026-09-16 found no statement that all hyperbolic groups are good, no
  problem-list entry, and nothing on goodness of `Sp(n,1)` lattices.

## Files

- `research/effaceable-cohomology-makes-inflation-an-isomorphism.md` (claim, established)
- `research/effaceable-cohomology-makes-inflation-an-isomorphism-proof.md` (route, direct)
- `research/torsion-free-hyperbolic-mod-p-classes-die-virtually.md` (new hole)
- `research/every-hyperbolic-group-good-via-rf-and-high-degrees.md` (route)
- `research/ghb7-degree-two-inflation-via-universal-rf.md` (route)
- `research/artifacts/hyperbolic-goodness-rf-plus-high-degree-reduction-2026-09-16.md`

check.sh on all six research paths: exit 0.

## Referee (2026-09-16)

**Checked.**

- *Direct proof `effaceable-cohomology-makes-inflation-an-isomorphism-proof`.* I redid
  the ladder chase in both directions. I checked (F3) by hand: `Φ(f)(h) = h f(h^{-1}U)`
  is a well-defined `Γ`-isomorphism `Map(Γ/U,M) -> Coind_U^Γ M` with `Φ(f)(1) = ε(f)`, so
  `σ∘η_* = res` holds. `H^n(G/U;Map(G/U,M)) = 0` for `n >= 1`. (F1) holds for arbitrary,
  not necessarily finitely generated, `G`, since the kernels of `G_hat -> G/U` form a
  basis of open normal subgroups. The proof is complete. One small gap is fixed:
  `(E_n)` gives some finite-index `W`, and the proof needs `U in N(G;M)`. The route now
  shrinks `W` to its normal core intersected with the kernel of the action. The
  criterion is classical (Serre's exercise), and no novelty is claimed.
- *Route `every-hyperbolic-group-good-via-rf-and-high-degrees`.* I checked Lemmas A-D,
  including the induction on `|M|` in Lemma D and its closure hypothesis, and the
  derivation. The `requires:` list is accurate. The only open inputs are
  `hyperbolic-finite-residual-is-torsion-free` and the new hole. The converse `1 => 2`
  follows from established nodes: `good-cocompact-proper-groups-are-virtually-torsion-free`
  item 3, `universal-hyperbolic-vtf-iff-rf`, and
  `good-groups-have-no-persistent-finite-cohomology`.
- *Route `ghb7-degree-two-inflation-via-universal-rf`.* I checked Lemma 6: `E_0 ∩ Z/n = 1`,
  `Q/(Z/n) ≅ K/N`, and the fibre-product map is injective and covers the identity. The
  derivation is correct. Its hypothesis is strictly implied by the hypothesis of the
  existing route `ghb7-degree-two-inflation-via-hyperbolic-goodness`.
- *Artifact Section 5 (GHB_2(7), cd <= 2) and Section 7 (Attempts).* The items used from
  `cckw-ghb2-kms-group-structure` exist as quoted. The Dehn-filling input of 7.3 is the one
  recorded on `hyperbolic-rf-question-equals-vtf-question`.
- *Duplicates.* `bin/cairn search --similar` on both new claims finds no duplicate. The
  nearest node is `finite-central-extension-rf-iff-virtually-splits`, and the artifact
  cites it as the central form of Lemma 2.2.
- *Citations spot-checked 2026-09-16.* I fetched the arXiv abstract pages of
  arXiv:2601.05706 (Hughes–Ng, 9 Jan 2026) and arXiv:2406.08639 (Boggi–Zalesskii, v1
  12 Jun 2024, v2 28 Oct 2024). Title, authors and dates match, and neither claims that
  all hyperbolic groups are good. The DOI 10.1215/00127094-2008-031 resolves to the GJZZ
  Duke 144(1) paper. Serre's and Brown's textbooks remain recalled, not fetched, and
  nothing in the graph depends on them.

**Changed.**

1. *Overclaim corrected* in the hole's Attempts, artifact §7.4 and the notes above. The
   claim was that for torsion-free cocompact `Sp(n,1)` / `F_4^(-20)` lattices "(b) is
   exactly goodness". Residual finiteness of the lattice does not give `(E_2)`, which
   needs residual finiteness of every finite-module extension, as Deligne-type examples
   show for general RF groups. The corrected statement: goodness is (b) on the lattice
   and its finite-index subgroups, plus that degree-two condition.
2. *Justification added* in artifact §5 (per-group sharpening) for "G good gives `(E_2)`
   for `H`". It is a Shapiro argument through
   `good-groups-have-no-persistent-finite-cohomology`.
3. *Normal-core shrinking made explicit* in the surjectivity step of the direct proof.

**Verdict.** Landed with fixes. Established: the effaceability criterion (for every
group, `(E_n) => (A_n)`). Also established, as honest conditional routes: universal
goodness of hyperbolic groups follows from Gromov's question (positive form) plus the new
hole `torsion-free-hyperbolic-mod-p-classes-die-virtually`; and Gromov's question alone
gives `ghb7-finite-index-subgroup-has-degree-two-inflation-surjectivity`. Open: both
inputs and the target.
