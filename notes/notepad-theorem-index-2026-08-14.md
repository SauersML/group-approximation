# NOTEPAD theorem index — 2026-08-14

Noncanonical scratch (notes/). Navigation aid for `notes/NOTEPAD.md`, produced by
cairn-archivist after four independent agents each rediscovered a different
unindexed result in that file on the same day.

## Why this exists

`notes/NOTEPAD.md` is 46,464 lines. Its newest dated header is `# 2026-08-12`, so
it reads as a stale progress log — but it contains **358 theorem-shaped
paragraphs**, many of them complete proofs that exist nowhere else in the
corpus and are not represented in the Cairn graph. Today alone, five results
were pulled out of it by three different agents, none of them indexed anywhere:

| line | result | pulled by |
| --- | --- | --- |
| ~9969 | sparse Clifford / orbital CE target | cairn-ce |
| ~20344 | single lamps recover the set action | cairn-ce, cairn-wreath, cairn-archivist (3x, independently) |
| ~22220 | unconditional hyperfinite HS stability of `St_5(L)` | cairn-archivist |
| ~26451 | profinite actions cannot retain a strict-compressor witness | cairn-ce |
| ~39199 | central-extension MF criterion | cairn-archivist |

**This index is a navigation aid, not a verification.** Nothing below has been
checked except the handful called out in the shortlist. A row here means "a
theorem-shaped paragraph starts at this line", nothing more. Claim it, read it,
verify it, then graph it.

## Shortlist — checked, and bearing on live frontier questions

These I read in full. Three are candidate eliminations, which is the class most
likely to be re-derived at cost.

- **L36722 — Theorem (permutation survival).** Slofstra's distinguished
  involution `J` survives a permutation ultraproduct, so `J notin Rad_sof(S)`.
  Refutes the assertion the corpus had isolated as `(HSC7)`. **Now graphed** as
  `slofstra-involution-not-sofic-radical` (+proof), invalidating the route
  `slofstra-solution-group-collision` into `sofic-radical-hyperlinear-survivor`.
  Second candidate lost to the same invalid inference — that exact
  finite-dimensional invisibility implies sofic-radical membership. The first
  was the literal mark (`literal-clifford-ce-model`).
- **L7584 — Lemma (central free-lamp normal form).** Thom's central free lamp
  `H_c = (*_Q Z) semidirect Ktilde` is **sofic**, via Elek--Szabó amalgamated-free-product
  permanence over the amenable `C = Z`, so it cannot be the counterexample.
  Ungraphed. A third candidate elimination.
- **L36280 — Lemma (central-dilation orientation).** If `alpha(Z) proper subset Z`
  for `Z <= Z(Ktilde)` central, the induced `alphaBar` on `Ktilde/Z` is
  surjective and noninjective, hence **cannot** be realized as `k |-> tkt^(-1)`
  in any overgroup. Ungraphed; a clean structural no-go on compressor
  realizability, relevant wherever a central dilation is proposed as a
  conjugation compressor.
- **L8008 — Theorem (rank-spiky compensation).** Sharpens what
  Alekseev--Thom Open Problem 6.2(a) would leave open: the compensating vectors
  exist in `L2` but necessarily have `||xi_n||_infinity -> infinity`. Ungraphed;
  6.2 is the nearest published open problem to this program.

## How to use the table

Sections repeat because the file is chronological, not thematic. Search by
section title first — the headers are unusually descriptive and often state the
verdict ("cannot", "no-go", "closes", "survives"). Then jump to the line.

| line | kind + name | section |
| --- | --- | --- |
| 729 | **Theorem** (unnamed) | Kazhdan-corner extraction for simple groups (2026-08-08) |
| 944 | **Lemma** Kazhdan square-root barrier for an exact ambient sector | Finite-quotient profile obstruction |
| 990 | **Theorem** square-root profile forces ambient Frobenius instability | Finite-quotient profile obstruction |
| 1047 | **Lemma** regular finite-quotient obstruction | Finite-quotient profile obstruction |
| 1164 | **Theorem** exact LHS reduction | Frobenius-stability status of the Kun--Thom ambient group (2026-08-08) |
| 3372 | **Theorem** W3 | Session 37: THE WIDTH-3 PROOF IS COMPLETE |
| 3488 | **Theorem** final gap | Session 38b: THE MIXING CASE IS SOLVED — the Ω-intertwiner argument |
| 3525 | **Lemma** (unnamed) | Session 38c: V-GENERATION PROOF (the last open item, now closed) |
| 5614 | **Lemma** uniform two-test obstruction, p-primary target | Quantitative strengthening: coordinatewise cycle surgery also fails |
| 5651 | **Lemma** uniform three-test obstruction, arbitrary target | Quantitative strengthening: coordinatewise cycle surgery also fails |
| 5913 | **Lemma** abelian diagonalization in a matrix ultraproduct | Abstract versus Cartan-preserving embeddings: the exact lifting gap |
| 5986 | **Theorem** MF Mautner decomposition | MF Mautner decomposition for an infranormal free lamp |
| 6053 | **Theorem** (unnamed) | Invariant ideals in the Laurent ambient are finite-codimensional |
| 6124 | **Theorem** single-trace criterion | A single trace-visible lamp witness is enough |
| 6194 | **Theorem** one-witness rank/defect criterion | Correct corner visibility criterion: one witness and Cesaro tensors |
| 6311 | **Lemma** uniform algebraic visibility | Fullness forces trace visibility, but the symmetric double has a fold |
| 6435 | **Theorem** Gaussian one-lamp criterion | Gaussian one-lamp criterion |
| 6518 | **Lemma** trace-gap/defect criterion | Audit of the proposed CIII hexagon: one vector is not enough |
| 6599 | **Lemma** truncated-Fock trace obstruction | Exact Bogoljubov implementers versus the free trace |
| 6664 | **Theorem** one-number Haar criterion | One-number Haar criterion: full freeness is unnecessary |
| 6807 | **Lemma** centralizer orbits of a transitive component | Kazhdan extreme-point audit: component selection does not create an er |
| 6872 | **Theorem** strict commutant compression criterion | Exact commutant-compression dichotomy: the minimal free-lamp face |
| 6935 | **Theorem** two extensions of one Gamma-model | Two-extension criterion: relative non-uniqueness already suffices |
| 6990 | **Lemma** (unnamed) | Exact finite-dimensional relative uniqueness |
| 7063 | **Lemma** faithful tensor completion | Faithfulness is free; an action-theoretic corollary |
| 7146 | **Lemma** many-cycle Prüfer calibration | The Prüfer tower alone does not force an ergodic centralizer |
| 7246 | **Lemma** finite central-orbit descent | Central-orbit descent and the exact p^m error loss |
| 7296 | **Lemma** regular-character camouflage | Lavi--Levit character rigidity cannot see strict commutant compression |
| 7365 | **Theorem** relative cocycle certificate | The exact relative-cocycle formulation |
| 7429 | **Theorem** amenable-sector normalization | Amenable Gamma-algebras cannot compress strictly |
| 7515 | **Theorem** regular-sector reduction | The nonamenable part reduces to the regular Laurent sector |
| 7584 | **Lemma** central free-lamp normal form | Thom's central free lamp is sofic and cannot be the counterexample |
| 7639 | **Lemma** Bass--Serre confinement | Shulman doubles cannot manufacture weak MF for the Leavitt witness |
| 7681 | **Lemma** the compressed subgroup has infinite index | The compressor has infinite index; regular tensor sectors are rigid |
| 7716 | **Lemma** relative FC-centre | The compressor has infinite index; regular tensor sectors are rigid |
| 7736 | **Theorem** regular tensor-sector rigidity | The compressor has infinite index; regular tensor sectors are rigid |
| 7785 | **Theorem** left--right infiniteness criterion | Strict compression is an infinite Kazhdan projection in the left--righ |
| 7854 | **Theorem** flexibly liftable models are compression-sterile | Ordinary and local HS-instability cannot supply the infinite projectio |
| 7930 | **Theorem** quantitative flexible-lifting gap | A strict witness has a quantitative flexible-lifting gap |
| 8008 | **Theorem** rank-spiky compensation | What Alekseev--Thom Open Problem 6.2(a) would still leave open |
| 8070 | **Theorem** binary-tree asymmetric near inclusion | Rank-spiky compensation already occurs for diagonal algebras |
| 8152 | **Corollary** tree-overlap strictness certificate | Rank-spiky compensation already occurs for diagonal algebras |
| 8198 | **Theorem** finite image of finite-dimensional unitary representations | Exact polynomial-elementary restrictions are compression-sterile |
| 8258 | **Theorem** endomorphism-orbit chains | Exact polynomial-elementary restrictions are compression-sterile |
| 8295 | **Theorem** macroscopic strictness on the orbit chain | Exact polynomial-elementary restrictions are compression-sterile |
| 8351 | **Corollary** the polynomial shear supplies the quotient tower | Exact polynomial-elementary restrictions are compression-sterile |
| 8420 | **Theorem** finite Schur multiplier of the stable Kun--Thom ambient | Scalar projective flux cannot assemble the shear chains |
| 8464 | **Theorem** asymptotically trivial scalar multipliers untwist | Scalar projective flux cannot assemble the shear chains |
| 8499 | **Theorem** central block curvature is flexibly negligible | Scalar projective flux cannot assemble the shear chains |
| 8531 | **Corollary** projective assembly is sterile | Scalar projective flux cannot assemble the shear chains |
| 8557 | **Theorem** transitive block curvature is stabilizer cohomology | Scalar projective flux cannot assemble the shear chains |
| 8596 | **Corollary** every stabilizer multiplier has the required block model | Scalar projective flux cannot assemble the shear chains |
| 8641 | **Theorem** congruence stabilizers supply unbounded projective holonomy | Scalar projective flux cannot assemble the shear chains |
| 8733 | **Lemma** Heisenberg stabilizer curvature has a uniform floor | Scalar projective flux cannot assemble the shear chains |
| 8777 | **Theorem** Bockstein--sparse-torsion equivalence | Scalar projective flux cannot assemble the shear chains |
| 8836 | **Corollary** the congruence criterion is unconditionally integral | Scalar projective flux cannot assemble the shear chains |
| 8911 | **Lemma** the congruence Bockstein is a cup-product carry | Scalar projective flux cannot assemble the shear chains |
| 8965 | **Theorem** virtual divisibility equals projective realizability | Rank three: scalable real holonomy is exactly virtual divisibility |
| 9022 | **Corollary** rank-three locally flat stabilizer curvature | Rank three: scalable real holonomy is exactly virtual divisibility |
| 9067 | **Lemma** fixed-prime divisibility is bounded | Hecke separation closes the fixed cuspidal-class tower |
| 9097 | **Lemma** continuous classes have the degree character | Hecke separation closes the fixed cuspidal-class tower |
| 9116 | **Theorem** no scalable virtually split cuspidal curvature | Hecke separation closes the fixed cuspidal-class tower |
| 9175 | **Lemma** finite-orbit concentration | Property `(T)` kills orthogonal-block symmetrization of the chains |
| 9203 | **Corollary** orthogonal orbit-chain assembly is sterile | Property `(T)` kills orthogonal-block symmetrization of the chains |
| 9342 | **Theorem** Bernoulli failure of relative `(T)` | The normal lamp kernel has no Kazhdan projection |
| 9409 | **Theorem** central torsion corner | Finite central torsion gives a profile-free weak-MF bridge |
| 9487 | **Lemma** central differences are characters | Perfectness obstructs centralizing a lamp-difference witness |
| 9533 | **Lemma** one central edge gives a relative character | Perfectness obstructs centralizing a lamp-difference witness |
| 9592 | **Corollary** finite central monolith | Central-monolith criterion |
| 9643 | **Lemma** cyclic Schreier kernel | The cyclic lamp has a nonsofic symmetric-double commutator |
| 9809 | **Theorem** weak-MF Clifford target | A central Clifford-lamp witness that would finish from weak MF |
| 9917 | **Corollary** one CAR trace suffices | Clifford-sector decomposition and the exact tracial target |
| 9969 | **Corollary** sparse Clifford target | Sparse orbital Clifford lamps suffice |
| 10004 | **Theorem** shrinking Clifford sector | Sparse central-sector profile: the exact HS threshold |
| 10073 | **Lemma** root restriction has density `1/(p^2+p+1)` | Rank-three finite parabolics have codimension-two Heisenberg curvature |
| 10198 | **Proposition** the optimal root-pair defect is `Theta(1/p)` | Rank-three finite parabolics have codimension-two Heisenberg curvature |
| 10264 | **Theorem** finite-image coefficient divisibility is bounded | Fixed finite-image coefficient classes are also Hecke-bounded |
| 10357 | **Theorem** Schur curvature localizes at density `Theta(p^(-3))` | A stronger varying class: sparse Schur curvature from `PSL_2(F_p)` |
| 10444 | **Theorem** integral-coefficient Kun--Thom pair | Integral coefficients synchronize the varying prime, but exact quotien |
| 10485 | **Proposition** coefficient-independent congruence sterility | Integral coefficients synchronize the varying prime, but exact quotien |
| 10520 | **Theorem** rank-four Schur curvature has density `Theta(p^(-12))` | A positive-cone-compatible Schur source in rank four |
| 10797 | **Proposition** global presentation support is at least quadratic | Binary-octahedral transfer aligns the source with a Soulé vertex |
| 10972 | **Lemma** orbitwise cyclic gauge | Cyclic presentation curvature is removable; the maximal parabolic is s |
| 11010 | **Proposition** maximal-parabolic 2-primary sterility | Cyclic presentation curvature is removable; the maximal parabolic is s |
| 11084 | **Theorem** full-trace similitude homogenization | Similitude homogenization makes the Jacobi sign full-trace |
| 11196 | **Theorem** asymptotically full cross-stabilizer channel | The Schur and Jacobi twists have a `1-O(p^(-3))` Mackey channel |
| 11270 | **Lemma** free outer root cycles | Fixed-compressor correction: unfold the outer order-`p` cycles |
| 11298 | **Theorem** fixed-compressor Schur--shear chain | Fixed-compressor correction: unfold the outer order-`p` cycles |
| 11465 | **Theorem** fixed-prime full Mackey channel | The Pauli--Jacobi channel also improves at fixed congruence depth |
| 11607 | **Theorem** simultaneous full Mackey channel | One coherent Pauli--Jacobi channel handles all three root orbits |
| 11676 | **Theorem** strict Heisenberg-cell microstates | A whole positive Steinberg triple has a strict Følner model |
| 11767 | **Theorem** simultaneous full Pauli channel | One Mackey product aligns all rank-two fibers simultaneously |
| 11987 | **Lemma** regular shared-root stabilization | Regular Heisenberg stabilization equalizes every shared root exactly |
| 12041 | **Theorem** strict maximal-unipotent cell | A maximal positive chamber has one strict `UT_4` Følner model |
| 12095 | **Lemma** finite regular absorption | Why regular stabilization does not yet couple the coefficient algebra |
| 12154 | **Theorem** asymptotically full Pauli--flag channel | The full-flag channel couples Pauli curvature directly to positive cha |
| 12315 | **Theorem** minimal two-chamber Steinberg cover | Minimal upgrade: two maximal-chamber orbits cover every Steinberg rela |
| 12370 | **Theorem** Thom-phase sterility on the affine parabolic | The two chambers generate the affine parabolic, but Thom's phase is tr |
| 12585 | **Theorem** multivariate square-zero jet covariance | A single square-zero jet ring solves the mixed-monomial subproblem |
| 12673 | **Lemma** finite Stone--von Neumann scalar-loop lemma | Stone--von Neumann kills every noncentral Fourier-gallery holonomy |
| 12729 | **Lemma** exact strict-star incidence | Orient the common star into the jet-depth chain |
| 12801 | **Lemma** equivariant cycle-origin lemma | Equivariant long-cycle lifts solve the finite incidence boundary |
| 12875 | **Lemma** coherent chamber lift | Chamber-orbit lifts make the rank-two incidence coherent |
| 12940 | **Lemma** exact micro--macro lift | The micro--macro carry cocycle gives exact depth covariance in each ch |
| 13009 | **Theorem** one-transition overlap reduction | The eight-chart overlap graph has only one Fourier edge type |
| 13072 | **Lemma** Weyl-atlas root connectivity | Correction: the eight-chart graph does not identify internal root occu |
| 13120 | **Lemma** full polarization transport | Polarization transport discharges the full adjacent-wall operator chec |
| 13177 | **Lemma** finite atlas to strict tracial compression | Faithfulness is tensorial; the exotic atlas only needs one order-one e |
| 13282 | **Lemma** the fixed-base pair is still a Kun--Thom pair | A fixed-base iterated-nilpotent Frobenius candidate |
| 13313 | **Theorem** fixed-base Frobenius flag | A fixed-base iterated-nilpotent Frobenius candidate |
| 13374 | **Theorem** iterated square-zero resolution | The Frobenius flag is an exact square-zero Heisenberg tower |
| 13462 | **Theorem** genuine layerwise Weil transport, odd `p` | Odd-prime Weil linearity removes the layerwise scalar obstruction |
| 13536 | **Theorem** graded Steinberg self-duality | Frobenius cyclicity identifies every cross-layer Steinberg tensor |
| 13584 | **Theorem** algebra-group affine Fourier model | One-shot affine Fourier linearization of the whole congruence kernel |
| 13670 | **Lemma** exact shear rank | Correction: the equal-cutoff Frobenius flag has macroscopic shear loss |
| 13783 | **Theorem** exact Fourier transform of an abelian extension | Fiberwise Fourier transform solves non-split extension coherence |
| 13879 | **Theorem** telescoping Weyl atlas | Separate compressor depth from Fourier depth, then telescope the atlas |
| 13938 | **Theorem** fixed-base global jet covariance | The auxiliary base variable makes the square-zero jet model global |
| 14056 | **Theorem** primal/dual generator audit | Generator covariance on the full split regular model |
| 14141 | **Theorem** bulk-word identity | The bulk-word estimate avoids a finite-presentation bottleneck |
| 14221 | **Lemma** explicit free-groupoid contraction | The free good-channel groupoid contracts the final scalar exactly |
| 14282 | **Lemma** the split elementary kernel is exactly additive | First adversarial audit of the fixed-base candidate |
| 14313 | **Lemma** one fixed witness works along the whole depth chain | First adversarial audit of the fixed-base candidate |
| 14527 | **Lemma** exact fusion-frame defect identities | Fusion-frame gluing is the exact quantum replacement for block inciden |
| 14604 | **Lemma** finite-atlas fusion estimate | Pairwise overlap error controls the entire fusion corner |
| 14674 | **Lemma** overlap transport propagates through the frame inverse | Transported witnesses preserve the frame range and cannot cancel |
| 14799 | **Theorem** finite quantum-atlas overlap estimate | Native good subspaces construct the common quantum atlas |
| 14959 | **Lemma** macroscopic well-conditioned frame corner | A fixed fusion cutoff removes every inverse-loss issue |
| 15217 | **Theorem** relative adjacent-wall intertwiner | Relative regular absorption constructs the missing adjacent wall |
| 15294 | **Theorem** flat multiplicity connection on the chamber atlas | One involutive multiplicity Fourier transform kills all atlas holonomy |
| 15343 | **Lemma** absorbed depth chains are strict only at the wrap | Correction: common regular absorption kills the macroscopic strict cha |
| 15566 | **Lemma** origin absorption propagates without becoming liftable | The absorbed factor must be pulled back along the face |
| 15609 | **Lemma** moving-wall propagation | The wall Fourier operator must move with the face coordinate |
| 15712 | **Lemma** pair-groupoid flatness | Moving wall bundles have exact, not merely scalar, atlas holonomy |
| 16000 | **Lemma** native-relator transfer | Relation transfer through nonorthogonal chart fusion |
| 16073 | **Lemma** conjugate cancellation | Conjugate tensoring kills the residual scalar `K_2`/Weil holonomy |
| 16438 | **Lemma** active signed-Weyl cell | Use auxiliary `GL_4` charts but keep the active ambient group `SL_4` |
| 17162 | **Lemma** (unnamed) | Exact matched-character cancellation lemma |
| 17267 | **Lemma** graded approximate descent | Balanced matched-character cancellation preserves the witness exactly |
| 17359 | **Lemma** enlarged-commutant energy | Kernel-compatible regular-quotient witnesses reduce to one membership  |
| 17458 | **Theorem** strict image-pair criterion | Image-pair endpoint: neither `K_2` descent nor faithful completion is  |
| 17638 | **Lemma** positive-chart criterion for two monomials | Audit correction: the chamber cover misses antipodal coefficient pairs |
| 17704 | **Lemma** row-torus automorphisms | Row-torus reduction closes the algebraic half of the antipodal gap |
| 17874 | **Lemma** equivariant regular absorption | Regular absorption makes a finite kernel grading exactly equivariant |
| 17995 | **Lemma** cyclic row-depth boundary estimate | Cyclic row-depth gauges remove the quantitative half of the row-torus  |
| 18191 | **Lemma** orbitwise normalizer | Orbitwise shear normalizers put the Heisenberg cell inside the jet reg |
| 18504 | **Lemma** equivariant transversal induction | Finite induction removes matrix-root synchronization exactly |
| 18545 | **Theorem** finite-normal quotients preserve soficity | Finite central layers of Thom's tower are not an obstruction |
| 18602 | **Lemma** simple-root semidirect decomposition | A simple-root complement gives one joint shear for an entire chamber |
| 18690 | **Lemma** selective row-owner intertwiner | Regular restriction gives the exact row-owner matching criterion |
| 18767 | **Lemma** prime-field shifted complement | The prime-field complement supplies the common owner copy for monomial |
| 19208 | **Lemma** fusion synchronization | Fusion rigidity: a high-rank atlas cannot average incompatible compres |
| 19282 | **Corollary** high-rank fusion is asymptotically a reference chart | Fusion rigidity: a high-rank atlas cannot average incompatible compres |
| 19697 | **Lemma** quotient-overlap ceiling | Quotient intertwiners have an exact kernel-rank ceiling |
| 19831 | **Theorem** free-word image pair | A noncommutative Kun--Thom pair from positive words in a free group |
| 20300 | **Lemma** finite-unit collapse | Every finite ambient free-word quotient collapses positive and inverse |
| 20344 | **Lemma** single lamps recover the set action | The 2026 sofic-action permanence theorem cannot make the Kun--Thom lam |
| 20695 | **Proposition** (unnamed) | The Clifford cover is itself nonsofic and has total finite-dimensional |
| 20898 | **Lemma** factor cocycle scalarization | Exact cocycle actions on one Clifford factor have only scalar curvatur |
| 21004 | **Theorem** tail-cocycle certificate | The direct CAR target is a tail `H^2`-vanishing problem |
| 21071 | **Theorem** no Bogoljubov tail coboundary | A tail trivialization cannot remain Bogoljubov |
| 21163 | **Theorem** finite-central-cover rigidity | Central covers cannot repair the Kun--Thom wreath obstruction (2026-08 |
| 21240 | **Theorem** all-central-cover rigidity | Central covers cannot repair the Kun--Thom wreath obstruction (2026-08 |
| 21302 | **Corollary** central-cover inheritance of a Kun--Thom witness | Central covers cannot repair the Kun--Thom wreath obstruction (2026-08 |
| 21335 | **Theorem** induced-character criterion | Induced characters force hyperfinite HS-stability (2026-08-09) |
| 21390 | **Corollary** stable elementary groups | Induced characters force hyperfinite HS-stability (2026-08-09) |
| 21436 | **Lemma** pullback of profinite closure | Relative profinite invisibility survives every full inverse-image exte |
| 21492 | **Theorem** universal-cover central rigidity | Kazhdan universal covers make every Leavitt central cover nonsofic (20 |
| 21664 | **Lemma** spectral-gap fixed-tail obstruction | The regular Bernoulli/CAR reservoir has no stabilizer-fixed tail (2026 |
| 21709 | **Corollary** no regular-reservoir coset lamp | The regular Bernoulli/CAR reservoir has no stabilizer-fixed tail (2026 |
| 21958 | **Theorem** finite-Lie representation conversion no-go | Uniform character gaps forbid hyperlinearizing finite-field rank model |
| 22096 | **Theorem** normalized-HS Leavitt trace floor | Direct tracial approximations of the coefficient ring have a sharp def |
| 22161 | **Theorem** HS-stability fork | Direct tracial approximations of the coefficient ring have a sharp def |
| 22220 | **Theorem** unconditional hyperfinite HS stability | Direct tracial approximations of the coefficient ring have a sharp def |
| 22262 | **Theorem** one-trace endpoint | Exact trace form of the unstable branch |
| 22336 | **Corollary** (unnamed) | The fork is exactly the hyperlinearity decision for the simple quotien |
| 22439 | **Theorem** (unnamed) | The explicit simple witness is omega-nonsofic |
| 22556 | **Theorem** flexible stability decision | The stability target can be weakened to flexible normalized-HS stabili |
| 22604 | **Lemma** finite positive cells | Root-cell exactification is automatic; global completion is the wall |
| 22625 | **Corollary** local flexible exactification | Root-cell exactification is automatic; global completion is the wall |
| 22691 | **Theorem** LLP certificate | A weaker nonhyperlinearity certificate: LLP instead of HS stability |
| 22881 | **Theorem** strict self-compression tower | The two-compressor relations force a strict von Neumann self-compressi |
| 23011 | **Theorem** wandering-cylinder/wreath decomposition | The compressor contains a bilateral Thompson--Bernoulli shift (2026-08 |
| 23105 | **Theorem** central amenable-near certificate | A one-character amenable-near certificate for the Clifford target (202 |
| 23166 | **Proposition** (unnamed) | The obvious exact Clifford representation is not amenable |
| 23203 | **Theorem** exact amenable sterility | Every genuine amenable representation kills the Clifford sign |
| 23305 | **Theorem** ambient-exact near sterility | The near model cannot keep the Kazhdan ambient group exact |
| 23401 | **Theorem** ambient flexible-instability certificate | The near certificate forces flexible HS instability of the ambient gro |
| 23508 | **Theorem** relative finite-cell correction | Relative flexible correction for a finite Steinberg cell (2026-08-09) |
| 23832 | **Theorem** intrinsic compressor separability | Compressor fibers are intrinsically LEF; the failure is ambient gluing |
| 23867 | **Corollary** the local coset action is LEF | Compressor fibers are intrinsically LEF; the failure is ambient gluing |
| 23943 | **Theorem** local quasi-regular coefficients do not extend | A sharp finite-dimensional extension gap at the compressor fiber |
| 24024 | **Theorem** profinite compression kernel | The obstruction has a nontrivial profinite kernel |
| 24087 | **Theorem** kernel transitivity | The profinite compression kernel is infinite |
| 24182 | **Theorem** universal compression projection | Strict Kazhdan compression makes the full group C-star algebra infinit |
| 24378 | **Theorem** Gaussian minus-infinity barrier | The quasi-regular Gaussian action has entropy minus infinity (2026-08- |
| 24478 | **Theorem** norm-MF Clifford sterility | The Clifford sign is invisible in every norm-matrix model (2026-08-09) |
| 24655 | **Theorem** rank-one character collapse | Rank-one root defects defeat every exact character amplification (2026 |
| 24732 | **Theorem** one-compressor calibration | A single separable compressor gives a sofic wreath product (2026-08-09 |
| 24850 | **Theorem** commutant holonomy survives adjoint amplification | Adjoint amplification does not dilute commutant-valued relator holonom |
| 24931 | **Theorem** central algebraic-envelope exclusion | Algebraic envelopes exclude every Proposition-2.3 witness (2026-08-09) |
| 25011 | **Theorem** transported stabilization | Prefix insertion is the exact unstable-`K_2` stabilization map (2026-0 |
| 25099 | **Lemma** endomorphism section | Uniform homological death splits the universal cover over deep corners |
| 25189 | **Theorem** local lifting through a universal central extension | Local homological death makes the central quotient locally liftable (2 |
| 25282 | **Proposition** exact `2`-Kazhdan reduction | The `2`-Kazhdan route reduces to the nontrivial coefficient sector (20 |
| 25341 | **Theorem** canonical prefix lift | The entire Thompson prefix-mixer subgroup lifts with zero holonomy (20 |
| 25408 | **Proposition** relative `(TT)/T` on the Leavitt self-copy | A proper Leavitt self-copy has relative `(TT)/T`; central quasi-cocycl |
| 25440 | **Lemma** Kazhdan central boundedness | A proper Leavitt self-copy has relative `(TT)/T`; central quasi-cocycl |
| 25462 | **Theorem** `(TT)/T` is invariant under Kazhdan central covers | A proper Leavitt self-copy has relative `(TT)/T`; central quasi-cocycl |
| 25559 | **Lemma** unique local chart lift | A finite superperfect leaf atlas presents the universal cover (2026-08 |
| 25587 | **Theorem** finite-atlas presentation of the universal central cover | A finite superperfect leaf atlas presents the universal cover (2026-08 |
| 25697 | **Corollary** unconditional first-corner splitting | Prefix stabilization kills the entire unstable multiplier in one step  |
| 25808 | **Lemma** uniform strong-division elimination | Global `(TT)/T` for the Leavitt elementary group (2026-08-09) |
| 25871 | **Theorem** (unnamed) | Global `(TT)/T` for the Leavitt elementary group (2026-08-09) |
| 26168 | **Theorem** (unnamed) | A finite exact-representation certificate with only one survivor (2026 |
| 26461 | **Theorem** (unnamed) | Profinite actions cannot retain a strict-compressor witness (2026-08-0 |
| 26615 | **Theorem** one-sided central-sector reduction | One-sided central-sector reduction for the two-cover atlas (2026-08-09 |
| 26868 | **Theorem** two-chart relation-module sequence | Exact relation-module form of the remaining unitary `H^2` problem (202 |
| 27661 | **Theorem** split-wreath Kazhdan obstruction | Split wreath products cannot realize the Kazhdan counterexample archit |
| 27708 | **Theorem** nonabelian Cohen--Lyndon quotient | Nonabelian Cohen--Lyndon lamps and the finite-support core obstruction |
| 27754 | **Theorem** finite-support core exclusion | Nonabelian Cohen--Lyndon lamps and the finite-support core obstruction |
| 27818 | **Theorem** amenable-quotient wreath-like permanence | Exact analytic boundary of the nonsplit wreath-like shortcut (2026-08- |
| 27856 | **Lemma** partial-product coherence floor | Exact analytic boundary of the nonsplit wreath-like shortcut (2026-08- |
| 27928 | **Theorem** corona-cocycle/splitting criterion | The unrestricted tail is an intrinsic corona cocycle (2026-08-09) |
| 28034 | **Theorem** almost-malnormal compressor exclusion | Hyperbolically embedded stabilizers cannot be Kun--Thom cores |
| 28126 | **Theorem** twisted Bernoulli phase-chart criterion | Finite phase charts for the twisted Bernoulli target (2026-08-09) |
| 28197 | **Theorem** finite-alphabet monomial collapse | Finite phase charts for the twisted Bernoulli target (2026-08-09) |
| 28289 | **Theorem** torsion rounding under cocycle stability | Cocycle-stable charts force the monomial model back to soficity |
| 28354 | **Corollary** cocycle-stable monomial collapse | Cocycle-stable charts force the monomial model back to soficity |
| 28442 | **Theorem** (unnamed) | Profinite-trace repair of the weak-MF symmetric double (2026-08-09) |
| 28480 | **Theorem** one-CE-trace fold criterion | Only one Connes-embeddable fold-difference is needed |
| 28572 | **Theorem** (unnamed) | The fold-difference is invisible in every exact matrix representation |
| 28641 | **Theorem** nonfaithful strict-compression criterion | Faithfulness is unnecessary in the strict-commutant criterion |
| 28702 | **Theorem** explicit sofic-radical element | The fold witness lies in the full sofic residual |
| 28784 | **Theorem** (unnamed) | The q=2 symmetric double has unique reduced trace |
| 28833 | **Theorem** complete sofic residual of the double | The complete sofic residual of the double and free lamp |
| 28885 | **Theorem** complete sofic residual of the free lamp | The complete sofic residual of the double and free lamp |
| 28927 | **Theorem** (unnamed) | An abelian-by-residually-finite nonsofic quotient |
| 28974 | **Corollary** (unnamed) | An abelian-by-residually-finite nonsofic quotient |
| 29004 | **Theorem** bounded-exponent sofic radical | An abelian-by-residually-finite nonsofic quotient |
| 29210 | **Theorem** strict nilpotent-chamber microstates | A full positive nilpotent chamber has one strict Følner model |
| 29360 | **Proposition** vertex-marginal blindness | Vertex-character rigidity cannot select the reduced double trace |
| 29534 | **Theorem** coefficient-independent perfect core | Every abelian KT lamp has the same perfect-core reduction |
| 29622 | **Theorem** integral Heisenberg KT cover | A perfect integral Heisenberg cover supplies growing-order Weyl phases |
| 29684 | **Theorem** one-character integral Weyl endpoint | A perfect integral Heisenberg cover supplies growing-order Weyl phases |
| 29738 | **Lemma** small-phase tensor amplification | Sublinear small-phase defect amplifies to the required CE character |
| 29823 | **Theorem** no Clifford character shortcut | The even Clifford one-character endpoint equals the canonical CAR trac |
| 29919 | **Lemma** integral Fourier quarter-turn | Fourier-odd curvature cancels while the Heisenberg phase doubles (2026 |
| 29942 | **Theorem** Fourier-odd curvature cancellation | Fourier-odd curvature cancels while the Heisenberg phase doubles (2026 |
| 29994 | **Theorem** finite-dimensional central blindness | Every finite-dimensional representation of the integral cover kills it |
| 30074 | **Theorem** transpose-time-reversal cancellation | Transpose time reversal cancels oriented curvature without cancelling  |
| 30154 | **Lemma** Weyl commutant gap | Quantitative Weyl scalarization of covariance defects (2026-08-09) |
| 30220 | **Lemma** dimension-free Weyl twirl | Quantitative Weyl scalarization of covariance defects (2026-08-09) |
| 30350 | **Proposition** even-cover norm-MF sterility | Cross-agent audit: the new Clifford weak-MF endpoint has a false premi |
| 30475 | **Theorem** centralizer shear | Abstract centralizer shear |
| 30499 | **Lemma** (unnamed) | A primitive radical word in the symmetric double |
| 30689 | **Theorem** spectral-rotation trace extraction | Antipodal norm models directly solve TRUE (2026-08-09) |
| 30764 | **Theorem** complete double radical | The complete sofic radical of the Kun--Thom symmetric double (2026-08- |
| 30866 | **Theorem** free-abelian full radical | Abelianizing the complete double radical (2026-08-09) |
| 30984 | **Theorem** Magnus--path model | The abelianized radical is the canonical path subgroup (2026-08-09) |
| 31069 | **Theorem** (unnamed) | A faithful transitive nonsofic action of a residually finite group (20 |
| 31135 | **Theorem** tempered Hilbert-quotient blindness | Every tempered Hilbert quotient kills the abelian radical (2026-08-09) |
| 31205 | **Theorem** mixing-cone obstruction | The radical detector cannot enter the regular/mixing cone (2026-08-09) |
| 31277 | **Theorem** Gaussian trace endpoint | The canonical faithful Gaussian trace on the path group (2026-08-09) |
| 31372 | **Theorem** positive-time Bernoulli recovery | Positive-time path heat recovers the full Bernoulli algebra (2026-08-0 |
| 31470 | **Lemma** stable Julia transposition | Stable Julia transposition isolates the twisted-double obstruction (20 |
| 31560 | **Theorem** tangent heat amplification | An infinitesimal heat model is enough (2026-08-09) |
| 31656 | **Theorem** Clifford central-limit tangent quantization | Clifford central-limit quantization closes the additive heat problem ( |
| 31797 | **Proposition** covariance budget | Exact covariance budget for composing with tangent amplification |
| 31861 | **Theorem** linear specialization of relative profinite closure | Profinite closure defeats every exact finite-dimensional linear detect |
| 31937 | **Theorem** cyclic-centralizer radical stabilization | Free stabilization makes the radical centralizer exactly cyclic (2026- |
| 32032 | **Theorem** torsion-class small-phase lift | Torsion central-extension classes admit trace-visible small phases (20 |
| 32089 | **Corollary** torsion classes cannot carry an infinite radical center | Torsion central-extension classes admit trace-visible small phases (20 |
| 32174 | **Lemma** finite-factor radical formula | The radical shear cannot extend to a vertex automorphism (2026-08-10) |
| 32189 | **Corollary** nonextendability of a radical shear | The radical shear cannot extend to a vertex automorphism (2026-08-10) |
| 32289 | **Theorem** centralization kills the radical | The double radical has no nonzero central quotient (2026-08-10) |
| 32321 | **Theorem** relative-abelianization formula | The relative-abelianization formula for every symmetric double (2026-0 |
| 32387 | **Theorem** infranormal relative-H1 vanishing | Infranormality closes the entire relative-H1 gate (2026-08-10) |
| 32446 | **Theorem** symplectic Kun--Thom pair | A symplectic Kun--Thom pair has a live scalar H2 flux (2026-08-10) |
| 32479 | **Theorem** nonzero relative real multiplier | A symplectic Kun--Thom pair has a live scalar H2 flux (2026-08-10) |
| 32590 | **Theorem** projective radical detector | Projective radical detection removes the o(t) scale requirement (2026- |
| 32712 | **Theorem** finite gauge-cover criterion | A finite gauge cover converts the relative H2 flux into an exact proje |
| 32870 | **Theorem** corona-covariance criterion | The cyclic radical shear is exactly one corona-covariance equation (20 |
| 32982 | **Lemma** Julia grading cancellation | The Julia minus sign is fold-invisible (2026-08-10) |
| 33049 | **Theorem** finite-gauge obstruction | A nontrivial relative multiplier has no finite gauge module |
| 33110 | **Theorem** periodic-sector rigidity | Periodic gauge sectors all kill the radical by the same scalar (2026-0 |
| 33167 | **Theorem** regularized gauge-character criterion | Every useful gauge character regularizes to one algebraic p.m.p. actio |
| 33254 | **Theorem** commutator-shear rank obstruction | The free-stabilized cyclic shear cannot repair rank blindness (2026-08 |
| 33312 | **Corollary** fixed-word spectral rotation is trace-circular | The free-stabilized cyclic shear cannot repair rank blindness (2026-08 |
| 33366 | **Theorem** finite-module invisibility | The projective gauge is invisible in every finite equivariant quotient |
| 33405 | **Corollary** periodic-point obstruction | The projective gauge is invisible in every finite equivariant quotient |
| 33463 | **Theorem** central-phase compactness | The finite gauge cover is not residually finite (2026-08-10) |
| 33520 | **Theorem** relative universal derivation | The projective gauge is a quotient of the relative augmentation lamp ( |
| 33657 | **Theorem** one-character gauge criterion | One Connes-embeddable gauge character is enough (2026-08-10) |
| 33748 | **Theorem** phase-splitting criterion | Phase splitting: locally equal projective sectors can retain a long co |
| 33874 | **Theorem** induced-character branch-cut criterion | Honest induced sectors reduce phase splitting to a finite-cover branch |
| 33968 | **Theorem** Kazhdan phase localization | Kazhdan uniformization localizes every long phase in the splitting coc |
| 34059 | **Theorem** sparse symplectic seam | The two-dimensional Weyl flux has a sparse seam gauge |
| 34155 | **Theorem** primitive moment symbol | Integral modular group rings have the required primitive Weyl symbol |
| 34228 | **Theorem** Kazhdan finite-image descent | Property (T) prevents the Weyl seam from extending over the polynomial |
| 34259 | **Corollary** the primitive moment sector cannot satisfy `(PST10)` | Property (T) prevents the Weyl seam from extending over the polynomial |
| 34300 | **Theorem** projective commutant centralization | The normal closure centralizes every finite projective commutant, quan |
| 34394 | **Theorem** action-level separation criterion | The gauge action is an explicit action-level hyperlinear-versus-sofic  |
| 34456 | **Theorem** Kazhdan collapse of invariant induced sectors | Kazhdan collapse also closes invariant induced-character sectors |
| 34560 | **Lemma** bounded root collision | A bounded root commutator closes all finite-index induced sectors |
| 34613 | **Theorem** finite-index induction no-go | A bounded root commutator closes all finite-index induced sectors |
| 34689 | **Theorem** rank-one star Gaussian quantization | Rank-one star fields remove the Clifford spin-determinant obstruction  |
| 34872 | **Proposition** target-class extraction | Separation of Alekseev--Bradford target classes is already the desired |
| 34946 | **Theorem** one-compressor sofic dilation | One strict compressor has an exact sofic automorphic dilation |
| 35011 | **Proposition** stable-finite obstruction to `(RSG13)` | Correction: the star profile is forbidden for the Kun--Thom vector |
| 35080 | **Theorem** Kazhdan induction dilution | Property (T) forbids induction of the one-compressor lamp (2026-08-10) |
| 35161 | **Theorem** internal-radical gap bridge | An internal radical spectral gap converts weak MF to hyperlinear nonso |
| 35271 | **Proposition** (unnamed) | For normal subgroups the internal gap is exactly property `(T)` |
| 35332 | **Lemma** quasi-regular test | The finite fixed-set hypothesis forces finite generation |
| 35349 | **Corollary** the symmetric-double radical has no internal gap | The finite fixed-set hypothesis forces finite generation |
| 35378 | **Proposition** (unnamed) | A finite subgroup of the sofic radical is abelian and essentially nons |
| 35433 | **Lemma** involutive pair-intertwining Julia lift | A relative Julia lift for an involutive edge intertwiner (2026-08-10) |
| 35539 | **Theorem** restricted-gauge obstruction | A nontrivial scalar flux has no restricted-wreath gauge (2026-08-10) |
| 35607 | **Proposition** exact relative-embedding gate | The direct-double trace gate is exactly relative embeddability (2026-0 |
| 35697 | **Theorem** Fourier-orbit decomposition of a central fiber | Fourier orbit form of the central gauge fiber, and the amenable-action |
| 35752 | **Proposition** invariant probability excludes topological amenability | Fourier orbit form of the central gauge fiber, and the amenable-action |
| 35795 | **Theorem** quantized finite-constraint defect | Finite constraint corners have a quantized covariance defect |
| 35821 | **Corollary** no finite invariant constraints in a transitive restricted | Finite constraint corners have a quantized covariance defect |
| 35864 | **Theorem** small diagonal corner gap | Property (T) rules out every shrinking diagonal constraint corner |
| 35914 | **Proposition** (unnamed) | The co-hyperlinear-subgroup shortcut is excluded (2026-08-10) |
| 35967 | **Theorem** full shrinking-corner gap | The shrinking-corner gap extends to the whole parent factor under ICC |
| 36019 | **Lemma** auxiliary-class separation | The action-class separation criterion cannot construct the first examp |
| 36059 | **Theorem** full-circle tensor envelope | Every infinite-order weak-MF element admits a full-circle model |
| 36142 | **Proposition** rank-spiky full-spectrum model | Full norm spectrum can be completely invisible to normalized trace |
| 36223 | **Theorem** (unnamed) | The characteristic-two symplectic Kun--Thom ambient is ICC (2026-08-10 |
| 36280 | **Lemma** central-dilation orientation | Thom's hyperlinear Kazhdan group does not supply a conjugation compres |
| 36340 | **Lemma** moment-to-rank visibility | Zeta23 rank--trace audit: an exact interface, not a missing source of  |
| 36405 | **Lemma** finite-image collision collapse | Honest finite-dimensional phase splitting is impossible for the binary |
| 36452 | **Theorem** finite-dimensional unitary-image rigidity | Honest finite-dimensional phase splitting is impossible for the binary |
| 36511 | **Theorem** intersection closure | Co-hyperlinear subgroups are closed under arbitrary intersections |
| 36556 | **Corollary** (unnamed) | Co-hyperlinear subgroups are closed under arbitrary intersections |
| 36617 | **Theorem** soficity-neutral homogeneous completion | The homogeneous solution-group completion preserves the soficity quest |
| 36722 | **Theorem** permutation survival | The Slofstra involution survives a sofic image |
| 36824 | **Lemma** finite-occurrence rank bound | Fixed free-word stabilization cannot repair a rank-spiky radical model |
| 36894 | **Theorem** zero-defect pointwise no-go | Pointwise unitary-to-permutation rounding is necessarily trivial |
| 37121 | **Proposition** (unnamed) | Normal-IRS / regular-character equivalence |
| 37450 | **Theorem** polarization/gauge Weyl no-go | Classical Weyl curvature survives every polarization and scalar gauge |
| 37634 | **Theorem** power-conjugacy rank blindness | Finite power self-similarity has no norm-to-trace force |
| 37831 | **Theorem** exact finite edge balance | The cyclic shear edge is exactly antipodally balanced at every even fi |
| 37920 | **Lemma** matrix rectification for a free source | 2026-08-10: what the quantum-polymorphism stable-commutativity theorem |
| 38009 | **Proposition** (unnamed) | 2026-08-10: the partial-orbit rounding method stops exactly at amenabi |
| 38142 | **Proposition** lamp-shift action detects soficity | 2026-08-10: the Bernoulli-lamp permanence hypothesis is already sofici |
| 38199 | **Lemma** simultaneous eventual separation | 2026-08-10: operator-norm MF conventions and the finite-normal theorem |
| 38303 | **Proposition** LRF auxiliary elimination | 2026-08-10: locally residually finite auxiliaries cannot witness the g |
| 38386 | **Lemma** single-witness reduction | 2026-08-10: one witness and one finite presentation suffice |
| 38411 | **Theorem** finite-presentation radical localization | 2026-08-10: one witness and one finite presentation suffice |
| 38451 | **Corollary** (unnamed) | 2026-08-10: one witness and one finite presentation suffice |
| 38489 | **Proposition** IRS core extraction | 2026-08-10: tensor powers extract the probability-one core of an IRS |
| 38552 | **Proposition** large relation-good spectral corner | 2026-08-10: spectral compression removes bad vectors but not the norma |
| 38911 | **Proposition** (unnamed) | 2026-08-10: the compact-unitary metric shortcut is false |
| 38962 | **Proposition** (unnamed) | 2026-08-10: the canonical Schoenberg--Poisson transform misses the fin |
| 39015 | **Theorem** Mackey parity pairing | The cyclic shear has a canonical exact Mackey sector (2026-08-10) |
| 39176 | **Theorem** regular MF symmetric doubles | The shear quotient is MF, but the finite kernel is exactly one project |