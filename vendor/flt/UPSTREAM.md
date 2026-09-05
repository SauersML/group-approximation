# FLT slice: a vendored reservoir, kept packed

This directory preserves a curated 2,344-module slice of Anthropic's Lean 4
formalisation of Fermat's Last Theorem as a **packed archive with a searchable
catalogue**, rather than as loose modules in the Lean library. It exists
because the user asked (2026-09-05) for everything useful in that repository
to be borrowed, while the fleet lead independently ruled that bulk copies must
not live under `GroupApproximation/` (see `notes/flt-repo-assessment-2026-09-05.md`
and the `.gitignore` rule for `GroupApproximation/ThirdParty/FLT/**`). Packed
here, the slice costs the fleet nothing: `scripts/check.py` walks only
`GroupApproximation/`, `scripts/remote-build.sh` rsyncs only
`GroupApproximation/`, `notes/`, `Palomar/`, `metadata/`, `scripts/` and a few
root files, and the snapshot sweep sees five small files and one archive.

- Upstream: <https://github.com/anthropics/fermats-last-theorem>, commit
  `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef` (Lean `v4.33.1`, Mathlib `v4.33.0`)
- Local target: Lean `v4.32.0`, Mathlib pin `81a5d257`
- License: Apache License 2.0 (`NOTICE` verbatim; `ATTRIBUTION.md` carries the
  upstream per-file notices for the files in this slice that contain material
  from the Imperial College London FLT project or from Mathlib)

## Files

| file | what |
|---|---|
| `flt-slice.tar.gz` | the slice, laid out as `GroupApproximation/ThirdParty/FLT/{Definitions,Theorems,P2M}` with imports already rewritten to `GroupApproximation.ThirdParty.FLT.*`, plus the aggregator `GroupApproximation/ThirdParty/FLT.lean` |
| `INDEX.md` | one line per theorem: upstream headline, Lean name, module |
| `STATEMENTS.md` | every theorem statement verbatim, grouped by namespace; grep it |
| `selection.json` | the seed list and the exact module closure |
| `ATTRIBUTION.md`, `NOTICE` | upstream notices |

Inventory: 1123 theorem modules, 1123 proof modules (`P2M/Sol/S_*`), 97
definition modules, `P2M/Util.lean`; 14.2 MB unpacked.

## Using a result from the slice

1. Find it in `INDEX.md` or `STATEMENTS.md`.
2. Compute its closure: the entry's module in `selection.json`'s `closure`,
   together with everything reachable from it through the `import
   GroupApproximation.ThirdParty.FLT.*` lines (a theorem module needs its
   `P2M/Sol/S_*` module and `P2M/Util.lean`; the proof module names the
   further theorem and definition modules it uses).
3. Unpack only those files at the repository root:
   `tar -xzf vendor/flt/flt-slice.tar.gz -C . <paths>`; they land under
   `GroupApproximation/ThirdParty/FLT/`, which `.gitignore` excludes, so add
   them with `git add -f` once they compile, and let the lead wire them.
   `Definitions/Def_Mathlib_Algebra_IsDirectLimit.lean` already lives there
   this way, for `Analysis/SequentialGroupColimitDirectLimit.lean`.
4. Expect Mathlib drift from `v4.33.0` to the pin: renamed or moved lemmas.
   `Definitions/Def_Compat_Mathlib430.lean` in the archive shows the flavour of
   shim the upstream itself needed.

## Upstream structure, and why the namespaces are not prefixed

Each `Theorems/Thm_X.lean` states one theorem and proves it by
`p2m_exact_reverting @P2MW.S_X.solution`; `P2M/Sol/S_X.lean` holds the proof
and its private lemmas in the namespace `P2MW.S_X`. Every file begins with
`import Mathlib`. The proof modules resolve names through the alias macros
`p2m_open` / `p2m_export` / `p2m_alias` of `P2M/Util.lean`, which look
declarations up by their upstream namespaces and silently skip names they
cannot find, so prefixing the declaration namespaces (as the HamSandwich port
does) would break every proof. Upstream names are FLT-specific or
`Def_Mathlib_*` shims; no clash with this development's declarations was found
by grep. Every API `P2M/Util.lean` uses exists in the Lean `v4.32.0` sources.

The slice keeps the upstream `set_option maxHeartbeats` bumps (245 lines;
`scripts/check.py` reports that class, and it already occurs on `main`) and
contains no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `implemented_by`,
`extern` or `native_decide` (lexical scan of every file).

## How the slice was chosen

Seeds: every upstream theorem whose Lean name lives in a generic Mathlib-style
namespace (`DoubleComplex`, `CochainCx`, `Matrix`, `Subgroup`, `IsFreeGroup`,
`SimpleGraph`, `QuotientGroup`, `AddCommGroup`, `AddSubgroup`, `AddMonoidHom`,
`Monoid`, `MonoidHom`, `Equiv`, `Function`, `Fin`, `Tuple`, `Finset`, `Nat`,
`Int`, `Multiset`, `Set`, `Finite`, `ENat`, `Complex`, `AnalyticOnNhd`,
`Manifold`, `Homeomorph`, `IsPreconnected`, `ContinuousMap`,
`ContinuousLinearMap`, `InnerProductSpace`, `Orthonormal`, `Summable`,
`MeasureTheory`, `Real`, `Sobolev`, `SchwartzMap`, `VectorFourier`,
`UnitAddTorus`, `AddCircle`, `HaarQuotient`, `HaarMeasure`, `exteriorPower`,
`GradedAlgebra`, `LinearMap`, `LinearEquiv`, `LinearIndependent`, `Module`,
`Submodule`, `TensorProduct`, `DirectSum`, `QuadraticForm`, `Polynomial`,
`MvPolynomial`, `CompleteOrthogonalIdempotents`, `TrivSqZeroExt`,
`IsLocallyConstant`, `Derivation`, `CategoryTheory`, `Topology`,
`TopologicalSpace`, `TopCat`, `IsOpen`, `Representation`, `RestrictedProduct`,
`SetLike`, `IncidenceSystem`), the group-cohomology cup-product Leibniz rule
and the Tate cup product commutativity and associativity, and the definition
files `Def_Mathlib_*`, `Def_Compat_*`, the Haar-measure and Haar-quotient
files, the double complex and bounded cochain tensor files and the cup-product
interfaces. The slice is the transitive import closure of the seeds inside the
upstream repository. Seeds whose closure entered the number-theory core (any
modular-form, Galois, elliptic-curve, adelic or quaternion-order definition
file, with more than twenty modules) were dropped, as were Deuring polynomials,
quaternion-order lattices, Frey packages, Haar measure on `GL₂(ℝ)` in Iwasawa
coordinates and one heavy `MvPolynomial` coefficient identity. The upstream
Newton identity `Matrix.charpolyRev_mul_prod_pow_eq_prod_pow_of_forall_trace_pow_eq`
is among the dropped: its closure carries the Frey-package definitions.

The lead's assessment is right that the upstream contains no singular
cohomology of spaces, characteristic classes, topological `K`-theory or
Borsuk–Ulam; what the slice holds is generic library material below that
level, listed next.

## Where the slice is meant to be used

- `DoubleComplex.*`, `CochainCx.*`: bounded double complexes, total
  cohomology, transpose, levelwise functoriality, the rows-exact augmentation
  edge isomorphism, exact-columns acyclicity, Euler characteristic, bounded
  spectral sequence convergence data, and the Künneth theorem for bounded
  cochain complexes over a field. Consumers: the cohomology-ring and `CP^n`
  lanes in `AlgTop/`.
- `IsDirectLimit`: already unpacked; `Analysis/SequentialGroupColimitDirectLimit.lean`
  makes the `K_1` tower colimit an instance, which gives it `IsDirectLimit.lift`
  and `IsDirectLimit.Equiv`.
- `Def_Mathlib_Topology_Algebra_{Group_Units,ContinuousMonoidHom,Module_Quotient,UniformRing}`,
  `Def_Mathlib_Topology_Bases`, `Def_Mathlib_IsModuleTopology`: topological
  groups of units, quotient topologies, continuous homomorphisms, for the
  unitary-component and `U(A)/U_0(A)` material in `Analysis/`.
- `Matrix.*`: the Euler-angle decomposition of `SU(2)`
  (`specialUnitaryGroup_fin_two_eq_diag_mul_rotation_mul_diag`); right-finite
  continuous functions on `U(n)` and `O(n)` are polynomial (Peter–Weyl
  adjacent); QR and Iwasawa-type decompositions; the elementary-matrix
  factorisation `exists_list_prod_elementary_eq_diagonal_of_det_map_mul_eq_one`
  (Whitehead-lemma territory for `K_1`); Selberg's lemma
  (`ProjGenLinGroup_exists_torsionFree_normal_subgroup_finiteIndex_of_fg_charZero`)
  and Minkowski's lemma
  (`GeneralLinearGroup_eq_one_of_isOfFinOrder_of_forall_sub_one_mem_of_ne`);
  free subgroups of `SL₂` by ping-pong; traces of powers. Consumers: `GGT/`,
  `Sofic/`, `Kazhdan/`, the `K_1` files in `Analysis/`.
- Group theory: `Monoid.CoprodI_nonempty_freeGroupBasis_fin_kuroshRank`,
  `IsFreeGroup.surjective_transfer_and_transfer_eq_one_iff_mem_closure`,
  `SimpleGraph.exists_walkConnected_transversal_of_preconnected` (Schreier
  transversals), `Subgroup.exists_exact_fundamental_domain_of_secondCountableTopology`,
  `Subgroup.card_orbitRelQuotient_mul_card_eq_index`,
  `Subgroup.exists_le_normal_subgroupOf_relIndex_ne_zero_torsionFree_of_relIndex_ne_zero`,
  `AddSubgroup.addGroup_fg_of_le_of_addGroup_fg`, the `AddCommGroup` torsion
  structure theorems, discrete subgroups of `ℝⁿ`. Consumers: `GGT/`, `Sofic/`.
- `Complex.*`: the argument principle
  (`circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt`), the residue
  theorem for simple poles, Jensen's inequality, polar coordinates on balls:
  winding numbers and the degree on `S¹`, for `KTheory/`.
- Compact operators: convolution operators on `L²` of a compact group are
  compact and symmetric, eigenspaces of a compact operator are finite
  dimensional, Hilbert–Schmidt kernel operators
  (`Def_Mathlib_MeasureTheory_Function_L2KernelOperator`), commuting operators
  preserve eigenspaces. Consumers: `Analysis/CompactIntegralOperator`, Peter–Weyl.
- `Representation.*`: complete reducibility for continuous representations of
  compact groups, absolutely irreducible representations, Schur-type
  centraliser statements, Brauer–Nesbitt in characteristic zero, `p`-group
  fixed vectors. Consumers: `Sofic/`.
- Measure theory: Haar measures on quotients (`HaarQuotient.*`), modular
  characters (`Def_HaarMeasure_HaarChar_*`), fundamental domains, Haar on
  restricted products, continuity of translation in `L²`. Consumers:
  `Analysis/CompactHaar`, amenability.
- `LinearMap.*` exact-sequence rank counting (nine-term exactness, Euler
  characteristic, dual exactness): long exact sequence bookkeeping in `AlgTop/`.
- Group cohomology: the cup product on inhomogeneous cochains with its
  Leibniz rule, the graded cup-product interface, and the Tate cup product's
  commutativity and associativity: a worked model for the graded
  commutativity that `AlgTop/CupProduct.lean` leaves open.
- `exteriorPower.*`, depth and Auslander–Buchsbaum, `Polynomial.*`,
  `MvPolynomial.*`: general algebra, no current consumer.

## Regenerating

`~/flt_borrow_work/` (outside the repository) holds `closure.py` (import
graph of the upstream), `select4.py` (seeds and pruning), `vendor2.py`
(rewrite, catalogue, archive) and `upstream.tar.gz` (the GitHub snapshot of
the commit above, 272 MB). Never unpack the whole upstream into the working
tree: it is 60,478 files, and its clone filled this machine's disk once.
