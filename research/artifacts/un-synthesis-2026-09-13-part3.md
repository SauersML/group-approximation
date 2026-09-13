# One ladder behind the non-MF paper and the Pestov 9.1 answer — synthesis, part 3 of 3

Lane `un-synthesis`, 2026-09-13, refresh 2 (main tip 938ae27b49). Status tags and review landings as in part 1.

## 11. The complexity face

[unreviewed; un-open-6.]
- **Measures are `Π⁰₁`** (`effective-subshift-invariant-measure-existence-is-pi01`). For effectively closed subshifts of a
  f.g. group with solvable word problem, existence of an invariant probability measure is `Π⁰₁`, uniformly. The proof
  uses frequency linear programs and Kolmogorov extension. Novelty: FOLKLORE (compare Hochman 2009).
- **The LEF type is `Π⁰₁`** (`effective-free-group-kazhdan-lef-type-is-pi01`). On effectively closed, minimal,
  topologically free `F_r`-subshifts:
  - "`EL_N(LC(X_e,F_q)⋊F_r)` is LEF in every rank" is exactly that `Π⁰₁` set;
  - "no MF quotient from some rank on" is its complement, witnessed by `Σ⁰₁` paradox certificates.
- **Contrast.** LEF recognition over all finite presentations is `Π⁰₂`-complete (`lef-of-finite-presentations-is-pi2-complete`).
  The dichotomy lowers the family to `Π⁰₁`.
- **[OPEN]** `effective-free-group-kazhdan-lef-type-is-pi01-complete`.

## 12. Continua and Turing degrees along the Pestov end

[unreviewed; un-open-5 bec8c05389, 7e6f1c8002; novelty: NEW (bounded), a routine corollary.]
- **The marking remembers the language** (`marked-subshift-elementary-group-determines-language`). Explicit group words
  `W_w`, independent of `X`, satisfy `W_w(σ_X) = 1` in `S_X` ⟺ `w ∉ L(X)`.
- **Continuum** (`continuum-many-simple-kazhdan-lef-groups`). For every `q` there are continuum many pairwise non-isomorphic
  infinite f.g. simple Kazhdan LEF groups, hence sofic and hyperlinear, with no finite quotient.
  - Continuum results exist for other classes (Ioana–Tucker-Drob, listing only). None was found for sofic simple Kazhdan
    groups.
- **Every Turing degree** (`every-turing-degree-is-a-simple-kazhdan-lef-word-problem`). The word problem of `S_X` is
  truth-table equivalent to `L(X)`, and `L(X_α) ≡_T α` for Sturmian `X_α`. So every degree is the word-problem degree of an
  infinite f.g. simple Kazhdan LEF group.
- **The dynamics lives in isomorphism type and word problem, not in the approximation rung.** Open:
  `subshift-elementary-group-isomorphism-forces-orbit-equivalence`.

## 13. Characteristic dependence: the Grigorchuk groupoid

[PASS · e6fc337462; un-open-3 9dcc91336e; credit CEPSS 1806.04362 and Nekrashevych IJAC 26.]
Let `𝒢` be the germ groupoid of the Grigorchuk group's self-similar action. It is ample, minimal and effective, with
Cantor unit space, and **not Hausdorff**. Put `R_q = A_(F_q)(𝒢)`.
- **Theorem A** (`grigorchuk-steinberg-algebra-simple-iff-char-not-two`). `R_q` is simple ⟺ `q` is odd. Characteristic
  enters only through the six equations for the four germs `z_e, z_b, z_c, z_d`.
- **Theorem B** (`grigorchuk-elementary-groups-simple-kazhdan-iff-odd-char`). For `n ≥ 3`:
  - `R_q` is finitely generated and carries a unital binary Leavitt family;
  - `EL_n(R_q)` is nonsofic with no MF quotient, for every `q`;
  - for `q` odd, `EL_n(R_q)/Z` is infinite, simple and Kazhdan (Theorem NH);
  - for `q` even it is not simple modulo centre, because of the singular ideal.
- **Reading.** For one non-Hausdorff groupoid, simplicity of the Kazhdan group reads off `q mod 2`, while its
  approximation profile (paradox side) does not change. The amenable residually finite Grigorchuk group sits inside a unit
  group with nonsofic elementary subgroups.

## 14. The boundary families

[All unreviewed except the headline instances of part 1 §5; un-boundary-families 0e439a2b56, 57c027734f, 4179e57149.]
- **Theorem B** (`paradoxical-cantor-actions-give-simple-kazhdan-not-mf`). Take a minimal, topologically free Cantor action
  of a f.g. group with a finite clopen family whose translates separate points (H-gen), and a paradoxical decomposition
  (H-par). Then `EL_N(LC(X,F_q)⋊Γ)/Z` (`N ≥ 3`) is infinite, f.g., simple and Kazhdan, and every `EL_n` (`n ≥ 2`) has no
  MF quotient.
  - (H-par) follows from minimality plus one north–south element.
- **Instances.**
  - **Family T** (`free-product-finite-groups-boundary-simple-kazhdan-not-mf`): `A*B` on its ends, e.g. `PSL_2(ℤ)`.
  - **Family P** (`p-adic-projective-line-elementary-simple-kazhdan-not-mf`): `⟨e_12(1), e_21(1), diag(p,1/p)⟩` on
    `P¹(ℚ_p)`, for every prime `p`.
- **Beyond transformation groupoids.**
  - **Theorem G** (`paradoxical-steinberg-elementary-simple-kazhdan-not-mf`): a f.g. Steinberg algebra of a minimal
    effective Hausdorff groupoid containing a full one-sided pair gives simple Kazhdan groups with no MF quotient.
  - **Instances:** `odometer-nekrashevych-elementary-simple-kazhdan-not-mf` and
    `product-two-graph-kp-elementary-simple-kazhdan-not-mf` (a rank-2 graph algebra; simplicity iff aperiodic and cofinal,
    `kp-algebra-steinberg-simple-iff-aperiodic-cofinal`).
- **[OPEN]**
  - `hyperbolic-group-cantor-model-simple-kazhdan-not-mf`: every non-elementary hyperbolic group with trivial finite
    radical should have such a Cantor model.
  - `boundary-kazhdan-families-pairwise-non-isomorphic`.

## 15. Examples and calibration refutations

| ring `R` | f.g. | simple | ring type | `EL_N(R)`, `N ≥ 3` | status |
|---|---|---|---|---|---|
| `L_k(1,2)`, `k` finite | yes | yes | not directly finite, `2[1] ≤ [1]` | Kazhdan, no MF quotient, nonsofic | printed; nonsofic OpenAI + Lean |
| `LC(X,F_q)⋊ℤ`, minimal subshift | yes | yes | exactly matricial | simple Kazhdan LEF | PASS, Lean |
| `LC(∂F_d,F_q)⋊F_d` | yes | yes | purely infinite | simple Kazhdan, no MF quotient, nonsofic, stable | PASS |
| free-group Toeplitz ring | yes | yes | exactly matricial | simple Kazhdan LEF | PASS · 10083fd646 |
| RF-group Toeplitz ring (Kazhdan `Γ` allowed) | yes | yes | exactly matricial | LEF Kazhdan | unreviewed |
| `LC(X,F_q)⋊Γ_p` (Abels–Prüfer) | yes | yes | rank model, not matricial | simple Kazhdan, linear sofic, not LEF | PASS · 560decb046 |
| Grigorchuk `A_(F_q)(𝒢)` | yes | iff `q` odd | Leavitt family | nonsofic, no MF quotient; simple mod centre iff `q` odd | PASS · e6fc337462 |
| Labbé `LC(Ω_U,F_q)⋊ℤ²` | yes | yes | rank model (polynomial complexity, unreviewed); matricial ⟺ torus tilings | linear sofic (via Σ⇐, unreviewed); LEF OPEN | §16 |
| `L_k(2,3)` | yes | — | non-IBN | no MF quotient for `N ≥ 3` | PASS · d60f405998 |
| `L_k(3,4)` | yes | — | non-IBN, module type `(3,4)` | no MF quotient for `N ≥ 4`; `N = 3` OPEN | §16 |
| odometer `LC(ℤ_2,F_q)⋊ℤ` | **no** | yes | exactly matricial | LEF, **no (T)** | PASS · 10083fd646 |
| Weyl `A_1(ℚ)` | no | yes | matricial over `∏ M_p(F_p)` only | LEF | PASS; FOLKLORE; duplicate nodes |
| `F_q[Γ]`, `Γ` amenable, not LEF | yes | no | stably finite, faithful rank | Kazhdan, linear sofic, **not LEF** | PASS; FOLKLORE |
| Toeplitz `J = F_2⟨s,t:ts=1⟩` | yes | no | defect not full | not MF (`N≥4`) but has an MF quotient: infinite middle regime | printed; unreviewed |

**Refutations every statement respects** (un-calibration; PASS · 10083fd646).
- **(F1)** Matriciality must be over *varying finite fields*: `A_1(ℚ)` has no char-0 model.
- **(F2)** Kazhdan families need finitely generated rings, so expansive actions, not odometers.
- **(F3)** A rank function plus stable finiteness does not give LEF.
- **(F4)** "No MF quotient" needs a *full* defect: `J` has a nontrivial MF quotient.
- **(F6)** [printed Prop l.1072] In positive characteristic, `EL_4(R)` MF ⟹ `R` directly finite.
- **Simplicity is essential for the root** (root Attempts F1): `ℤ[L^×]` is stably finite yet its `EL_n` are not MF.

## 16. The open middle

- **(M⇐)** `stably-finite-simple-rings-have-mf-elementary-groups`, i.e. "for simple rings the middle MF regime is empty".
  The first test ring is the Abels–Prüfer ring of §8.5.
- **(Σ⇒)** `linear-sofic-el-groups-force-rank-model`.
- **The Labbé ring** `labbe-wang-shift-crossed-product-is-exactly-matricial` [OPEN].
  - **Torus criterion** [PASS · 72ff092a72; `torus-quantum-tilings-decide-matriciality-of-sft-rings`]. For free minimal
    ℤ²-SFTs over finite `k`, exact matriciality ⟺ for every `D` some torus `ℤ²/Λ` carries a nonzero finite-dimensional
    module of the translation-free torus tiling algebra.
  - **Growth** [PASS · 72ff092a72, display GAP fixed; `sft-tiling-module-dimensions-and-periods-must-diverge`]. Witness
    dimensions and period tori must diverge.
  - **Rank side** [unreviewed]: polynomial complexity gives a rank model, hence linear soficity of the Kazhdan groups.
  - **LEF consequences.** If the ring is finitely presented, no `EL_N` (`N ≥ 4`) over it is LEF (un-lef-converse §4). The
    tiling route certifies non-LEF only through crux (C2).
  - Owner lanes: un-labbe-ring, ex2/ex3 Labbé lanes.
- **The low-rank band** `el-n-mf-quotient-below-twice-paradoxical-level-exists` [OPEN].
  - For `L_k(3,4)` only `N = 3` is open (`el3-leavitt-3-4-has-full-mf-radical` reduces it to
    `leavitt-3-4-module-iso-image-normally-generates-e3`).
  - **Firewall** [unreviewed; un-low-rank-band 92fa30e814]. For `L_K(m,n)`, no column of a module isomorphism at module
    rank `m` is completable, so neither "an `E_m`-image of `e_1`" nor "a free coordinate" can close the band. The only
    route left is non-completable transvections that normally generate `E_3`.
  - A nontrivial MF quotient of `EL_3(L_k(3,4))` would be a new object: a Kazhdan group with an MF quotient inside `EL_4`,
    which has none.
- **Measure without towers in char p:** `invariant-measure-gives-rank-function-any-field` (Kaplansky-hard), and
  `type-semigroup-reflects-paradox-of-steinberg-algebra`.
- **Soficity on the measure middle:** `free-minimal-subshift-elementary-groups-are-sofic` (Arzhantseva–Păunescu Q 8.5 at
  `S_N`).
- **Hyperlinearity on the paradox side:** `boundary-action-simple-kazhdan-group-is-hyperlinear`, famous either way. The
  HS analogue of Lemma C is `hyperlinear-groups-kill-rigid-compression-defects`.
- **Reduced MF on the measure side:** `free-group-cantor-el-n-reduced-cstar-mf-iff-invariant-measure`.
- **Coarse and computability:**
  - `paradox-side-elementary-group-is-finitely-presented`;
  - `elementary-group-lef-growth-separates-subshifts`;
  - `effective-free-group-kazhdan-lef-type-is-pi01-complete`;
  - `subshift-elementary-group-isomorphism-forces-orbit-equivalence`.
- **Families:**
  - `measure-rf-class-is-exactly-virtually-free-groups`;
  - `hyperbolic-group-cantor-model-simple-kazhdan-not-mf`;
  - `boundary-kazhdan-families-pairwise-non-isomorphic`;
  - `steinberg-gl-max-mf-quotient-is-low-degree-homology`;
  - `hilbert-hotel-radical-is-reached-in-one-step`.

## 17. Status ledger

- **PASS.**
  - Simplicity: S4 and its three ingredients, Theorem NH, Grigorchuk A/B, the Steinberg and CEPSS imports.
  - Ladder rungs: (L⇐), (L⇒) with `lef-elementary-groups-force-lef-rings` and `simple-lef-rings-are-exactly-matricial`,
    (Σ⇐), (M⇒).
  - Paradox side: ring Tarski, KMP import, Theorem P (three nodes), non-IBN, the groupoid no-measure theorem (two nodes),
    the bridge, the Rainone–Sims and ABBL imports, unperforated purity, char-0 dichotomy.
  - Measure side: the algebraic Tarski chain, the char-0 rank function, local matrix models, RF ⟹ matricial, matricial ⟹
    measure, the Kerr–Nowak import, the free-group ring equivalence, ℤ² quantum tilings, torus criterion, divergence.
  - The flagship.
  - Objects: the Toeplitz free-group family; the boundary headline and families (after scope repair); boundary
    nonsoficity, the Leavitt family and the Lean input; stability ⟺ nonsofic; halvable corners; purely infinite stable
    nonsofic; the middle rung, its Følner rank models and the group embedding.
  - Traces T0–T5 (with credit and naming fixes).
  - MF spectrum monotonicity and rescaling; the calibration rows C1–C3; `finitely-presented-lef-groups-are-residually-finite`.
- **Unreviewed.** Lemma C and linear images; the Hilbert-hotel radical and sandwich; the Toeplitz middle regime; the
  unit-group face; rank models by growth and complexity; the 𝔑 class and RF-group Toeplitz rings; reduced-C* nodes; the
  coarse face; complexity; continua and Turing degrees; boundary Theorem B, Families T/P, Theorem G and its instances;
  low-rank firewall.
- **OPEN.** The root, (Σ⇒), (M⇐), and every item in §16.

## 18. Credits and novelty

- **Carried prior work:**
  - Ershov–Jaikin-Zapirain (T);
  - Steinberg, BCFS, Clark–Edie-Michell, CEPSS (simplicity and centre);
  - **Stepanov 1997** (normal-subgroup method);
  - **Beuter–Gonçalves 2018** (crossed products as Steinberg algebras);
  - Clark–Sims (Leavitt as Steinberg);
  - Rainone–Sims, KMP, ABBL, Goodearl–Handelman (Tarski);
  - Larki (pure infiniteness);
  - Kerr–Nowak and Ma (residually finite actions);
  - Grigorchuk–Medynets (LEF full groups);
  - Elek and Ara–Claramunt (rank models);
  - Gao–Jackson–Seward (free subflows);
  - Abels (Abels–Prüfer group);
  - **Schafhauser 2017** and Rainone–Schafhauser (MF traces);
  - Kirchberg 1994, Ozawa, Brown Mem. AMS 184 (traces of Kazhdan groups);
  - Magee–de la Salle (invariant-vector obstruction);
  - Vershik–Gordon, Malcev, Elek–Szabó;
  - Ara–Goodearl–Pardo, Ara–Brustenga–Cortiñas, Matui (units, `K_1`, homology);
  - Spielberg 1991;
  - **OpenAI 2026-08-01** (nonsoficity of `L_(F_2)(1,2)^×`, the first nonsofic group).
- **Bounded novelty** (un-novelty parts 1–2):
  - **NEW (bounded):** the free-group dichotomy as a group-level statement; the local-annihilation criterion as stated;
    the threshold theorems as routine corollaries of tex l.918; the ring-level combinatorial-model equivalence; the
    continuum of simple Kazhdan LEF groups (routine).
  - **New example, not a first:** `S_∂`.
  - **FOLKLORE:** ring Tarski; the Weyl calibration; group-ring LEF; exactly matricial ⟹ LEF ring; the `Π⁰₁` upper bound;
    stability ⟺ nonsofic (likely).
  - **PRIOR:** the MF-trace concept; the Kazhdan trace collapse; the `K_1` formula; the full-group LEF theorems; the
    crossed-product dictionary; the exchange-ring simplicity case.
- **Before public framing:** decide local annihilation versus Stepanov's condition (b), and read Vaserstein LNM 854.
  MathSciNet and zbMATH were not reached by any novelty pass.
