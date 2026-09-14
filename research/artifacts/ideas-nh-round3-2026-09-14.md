# Ideas, round 3: a non-hyperlinear group (2026-09-14)

Lane `ideas-nh-round3`. Target: `non-hyperlinear-group`.

**Outcome.**
- All sixteen ideas were killed or found already on main.
- The one surviving round-2 idea, quantum tiling hosts, was executed. It is now a theorem that removes it as a source of non-approximability: `translation-invariant-lcs-hosts-localize-to-box-patches`.
- No uncovered survivor with leverage remains. Ranked existing routes and one recommended deep lane are in §4.

## 0. Pins

These statements were read at source by the lanes that landed the named nodes. This lane quotes those nodes and did not re-read the papers.

- **MIP* = RE** (`mipstar-equals-re`). Ji--Natarajan--Vidick--Wright--Yuen, arXiv:2001.04383, Theorem 12.9 and Corollary 12.10. A polynomial-time map `M -> G_M` to nonlocal games has two properties:
  - if `M` halts, `val*(G_M) = 1`, attained by a finite-dimensional projective, consistent, commuting strategy;
  - if `M` does not halt, `val*(G_M) <= 1/2`.
- **Why MIP* = RE does not give a non-hyperlinear group.**
  - Paddock--Slofstra Example 4.2 (`mipstar-bcs-tracial-nonru-exists`) gives a finite Boolean constraint system with a tracial but no `R^U` model. That is a non-embeddable *algebra*.
  - Paddock--Slofstra Proposition 5.8 (`lcs-tracial-ru-gap-equiv-nonhyperlinear`) says the same gap for *linear* systems is equivalent to a finitely presented non-hyperlinear group. Their Lemma 5.7 is the dictionary: tracial satisfiability iff `J != 1`, and R^U-satisfiability iff `J` is nontrivial in approximate representations.
  - Paddock--Slofstra, p. 4, quoted in `research/artifacts/ex-nh-mipstar-quantum-symmetry-rung-2026-09-12.md` §1: "it is not possible to embed every BCS algebra in the BCS algebra of a linear system game. This is an obstacle for one method of constructing a non-hyperlinear group that tends to come up when discussing potential consequences of MIP*=RE."
  - Mechanism: the trace-selection gap. A group algebra carries the coaction `g |-> g ⊗ g`, whose invariant state is the regular trace. A MIP*-derived non-embeddable trace is selected by no symmetry.
  - Source chains stop before linear syntax: `lin-ji-mastel-slofstra-stop-before-lcs` and the `jnvwy-*` affine-safety nodes.
- **Slofstra embedding** (`slofstra-solution-group-embedding-preserves-marked-involutions`). Every finitely presented `G` with a central involution `J'` and involutions `w_i` embeds effectively in a solution group `Gamma(H,b)`, with `phi(J') = J` and `phi(w_i) = x_(e_i)`. The embedding carries no matrix-soundness estimate.
- **Dogon--Vigdorovich**, arXiv:2506.20843v2:
  - Theorem 1.3 (`hs-stability-forces-nonhyperlinear-central-extension`): (T;FD), a central `Z`-extension with finite abelianization, and HS-stability give a non-hyperlinear finite central extension.
  - Theorem 4.1 (`dv-s-arithmetic-hs-stable-nonhyperlinear-extension`): the S-arithmetic instance, including `SL_2(Z[1/p])`.
  - Theorem 1.6 (`character-rigidity-equals-hyperfinite-hs-stability`): for higher-rank lattices with (T;FD), hyperfinite HS-stability, character rigidity and robust (T;FD) are equivalent.
- **Dogon**, arXiv:2211.10492v3, Corollary 1.9 (`dogon-sp2g-weak-ucp-nonhyperlinear`): weak ucp-stability of `Sp_(2g)(Z)` makes Deligne's universal-cover lattice non-hyperlinear.
- **Stability-based separation.** Main carries `hyperlinear-flexibly-hs-stable-group-is-residually-finite`, `finitely-presented-local-hs-stable-non-rf-is-nonhyperlinear` and `hs-stability-plus-fd-residual-forces-nonhyperlinearity`. Their titles were read; their statements were not re-read by this lane.

## 1. Walls not re-proposed

- **W1. Equivalence only.**
  - Existentially closed hosts (`b96da8433`) and Diracization (`diracization-gap-equals-nonhyperlinear-group`) give equivalences, not reductions.
  - So does the Leavitt character simplex (`binary-leavitt-full-character-simplex`). `H = L_(F_2)(1,2)^x` has characters `a 1 + (1-a) delta_1`, so `H` is hyperlinear iff every character is Connes embeddable iff `delta_1` is.
- **W2. Trace selection and affine safety** (§0).
- **W3. Permutation-specific steps.**
  - Kun--Thom KT3 (an exact orbit partition at every finite stage) and KT4 (integral isotropy medians) have no Hilbert--Schmidt transcription (`research/artifacts/hl-hyperlinear-vs-sofic-2026-09-13.md` §6).
  - What transfers is the win-win `hyperlinear-groups-kill-rigid-compression-defects`.
- **W4. Frames.** Approximately masa-normalizing microstates are equivalent to Q3.4 affirmative (`hyperlinear-groups-admit-masa-normalizing-microstates`). Every nonsofic group, the Leavitt unit group among them, has no such microstates.
- **W5. Open stability hypotheses.** Dogon--Vigdorovich HS-stability, weak ucp-stability and LLP of `C*(Sp_(2g)(Z))`.
- **W6. The nonsofic witnesses.**
  - `binary-leavitt-unit-group-is-permutation-stable` (unreviewed): every almost-homomorphism into symmetric groups is asymptotically trivial.
  - Hyperlinearity of every established nonsofic witness is open in both directions (`hl-hyperlinear-vs-sofic` §1).

## 2. Ideas and kill tests

Each entry gives the mechanism, why it might beat the walls, the kill test, and the verdict.

1. **Hamming P-stability to HS for `H`.**
   - Mechanism: rerun the permutation-stability argument (a limit character plus the character simplex) for HS almost-homomorphisms.
   - Why: nonsoficity is established, and the argument does not use permutations until the last step.
   - Kill test: does the HS version need more than "`delta_1` is not Connes embeddable"? No. Limit characters of HS almost-homomorphisms are Connes embeddable, so HS-triviality is equivalent to `delta_1` not being embeddable, i.e. to non-hyperlinearity of `H`.
   - Verdict: dead, equivalence (W1).
2. **Monomial rounding.**
   - Mechanism: take microstates in `U(1) wr S_n` and round the phases to `mu_m` with a random offset. Since `mu_m wr S_n ⊂ S_(nm)` preserves Hamming distance, this gives permutation models. `tau ~ 0` forces fixed-point fraction `<= 1/2 + o(1)`, and tensor amplification gives soficity.
   - Consequence: nonsofic groups have no approximately monomial microstates.
   - Kill test: is this on main? Yes: `leavitt-units-admit-no-bounded-block-monomial-hs-model` and `block-monomial-hs-models-sofic-mod-amenable-soft-kernel`. The general frame claim is equivalent to Q3.4.
   - Verdict: dead, covered (W4).
3. **Error-basis exactness.**
   - Mechanism: for unitaries normalizing a nice error basis, distinct basis elements (up to phase) are at HS distance `>= sqrt 2`.
     - Normalizer defect `< 1/sqrt 2` then induces an exact homomorphism to the finite symplectic group.
     - A minimally almost periodic perfect group therefore has no such models.
   - Kill test: the model class is exact normalizers only. The recovery statement `hyperlinear-leavitt-models-reduce-to-error-basis-normalizers` is OPEN and implies non-hyperlinearity. The exclusion `leavitt-24k-models-avoid-blockwise-error-basis-normalizers` is already on main.
   - Verdict: dead, covered.
4. **Factorization property.**
   - Mechanism: Kirchberg's theorem, (T) plus factorization property implies residually finite, applied to Deligne covers.
   - Kill test: `hyperlinear-groups-have-factorization-property` is refuted by Thom's sofic Kazhdan groups without the factorization property.
   - Verdict: dead.
5. **LLP of `C*(Sp_(2g)(Z))`.**
   - Mechanism: LLP gives weak ucp-stability, hence a non-hyperlinear Deligne cover (Dogon Corollary 1.9).
   - Kill test: this is `dogon-sp2g-weak-ucp-nonhyperlinear` with `sp2g-z-full-c-star-algebra-has-llp` open. Lane `hl-nh-deligne-extension` runs on these covers.
   - Verdict: covered; not duplicated.
6. **S-arithmetic HS-stability.**
   - Mechanism: Dogon--Vigdorovich Theorem 4.1 for `SL_2(Z[1/p]) = SL_2(Z) *_B SL_2(Z)`.
   - Kill test: already on main, including the Iwahori lane. Theorem 1.6 makes stability equivalent to character rigidity plus robust (T;FD).
   - Verdict: covered.
7. **Kervaire--Laudenbach or nonsingular-system failure.**
   - Mechanism: Nitsche--Thom show equations with invertible exponent data are solvable over hyperlinear groups, so a failure refutes hyperlinearity.
   - Kill test: on main as `kervaire-laudenbach-holds-for-hyperlinear`, `kl-violation-refutes-hyperlinearity-route` and `thompson-v-not-hyperlinear-from-kl-violation`. The balanced census `ffcfaa7d0` is negative to length 15.
   - Verdict: alive as an existing route (the KL lanes); not new.
8. **MIP* BCS gap to LCS.**
   - Verdict: covered by W2, and equivalent to the goal by Proposition 5.8.
9. **Barrington / nonabelian-coefficient constraints.**
   - Mechanism: write non-affine Boolean checks as word equations in `A_5`, as in Barrington's width-5 programs. For a `K`-valued variable, a PVM `{P_g}` gives `V = sum_g P_g ⊗ lambda(g)` on `H ⊗ C[K]`.
     - `V` commutes with `1 ⊗ rho_right(K)`.
     - The PVM condition is exactly the group relation `V_12 V_13 = W V_12 W^(-1)`, with `W(e_a ⊗ e_b) = e_a ⊗ e_(ab)`, which conjugates `lambda(g) ⊗ 1` to `lambda(g) ⊗ lambda(g)`.
     - So gradedness is a group relation over a finite constant group.
   - Kill test: can group relations select the permutation isotypic sector of the constant group? No. Relations hold in every representation of the finite constant group, so the construction reduces to sector selection. Main already stops there:
     - the balance barrier `clifford-groupified-control-is-forced-balanced`;
     - the S3 packets `every-predicate-has-s3-equivariant-raw-radical-drop`, which stop at the coordinate atlas;
     - affine torsor port profiles, `torsor-cfi-port-profiles-are-cosets`.
   - Verdict: dead, reduces to sector selection.
10. **Quantum tiling hosts `Sol ⋊ Z^d`** (the round-2 survivor, `nh-games.md` Approach 4).
    - Executed in §3.
    - Verdict: dead as a source of non-approximability; host gaps are finite box gaps.
11. **Free entropy dimension.**
    - Mechanism: microstate dimension against L²-Betti bounds.
    - Kill test: for a hyperlinear Kazhdan group, `beta_1^(2) = 0` bounds the dimension by 1, which embeddable diffuse algebras satisfy. No contradiction. The literature bounds are recalled, not re-verified here.
    - See also `cstar-one-bounded-entropy-is-canonical-trace-blind`.
    - Verdict: dead.
12. **Sphere-net discretization.**
    - Mechanism: a unitary almost-representation acts on the unit sphere; match a fine net to its image to obtain permutations.
    - Kill test: Hamming almost multiplicativity needs exact agreement, but metric closeness only gives agreement up to `3 delta`, which does not round. The spherical almost-action is also a genuine measure-preserving action, and such actions exist for every group. This is the same wall as the `hyperlinear-implies-sofic-via-*` routes.
    - Verdict: dead.
13. **Hilbert--Schmidt Burnside** (Tarski monsters of prime exponent, free Burnside groups).
    - Verdict: covered by `hyperlinear-fg-bounded-exponent-groups-are-finite` (OPEN; equivalent to trace rigidity of approximate exponent-N models).
14. **New host families** (recalled, not re-verified here).
    - Burger--Mozes lattices act properly on a CAT(0) square complex, so they have the Haagerup property; there is no rigidity lever.
    - Golod--Shafarevich Kazhdan groups give infinite residually-p images, which are hyperlinear, and say nothing about the kernel.
    - Kac--Moody simple lattices, if character rigid, fall in the equivalence family of idea 1 (`character-rigid-fp-simple-groups-stability-dictionary`).
    - Toledo's non-residually-finite Kähler groups lack (T;FD), so the Dogon--Vigdorovich mechanism does not apply.
    - Verdict: dead.
15. **Strong (T) projections** (Lafforgue, de la Salle).
    - Kill test: only genuine representations of small exponential growth extend to the Banach completions; almost-representations do not.
    - Verdict: dead.
16. **Existentially closed hosts, forcing.**
    - Verdict: covered by `b96da8433` (equivalences only).

## 3. Executed: tiling hosts localize to box patches

Nodes: `translation-invariant-lcs-hosts-localize-to-box-patches` (claim, ESTABLISHED, unreviewed) and its route `translation-invariant-lcs-hosts-localize-to-box-patches-proof`.

- **Setting.** A translation-invariant binary linear rule on `Z^d` with context radius `R`. Its host `Gamma = Sol ⋊ Z^d` is finitely presented; `P_N` is the solution group of the box system on `[0,N)^d`.
- **Box to host.**
  - An `(eps,J)`-model of `P_N` induces, on `H ⊗ C^(Z_N^d)`, a model of `Gamma` with defect `<= eps + 2 sqrt(dR/N)`.
  - In it the translations commute exactly and `t_i^N = I`.
  - Only the `<= dR/N` fraction of seam copies breaks relators.
- **Host to box.**
  - An `(eps,J)`-model of `Gamma` restricts to `P_N` with defect `<= (1 + 3 L_c d^2 N R) eps`.
  - The cost comes from reordering `t_1^(y_1)...t_d^(y_d)` against approximate commutation.
  - No HS-stability of `Z^d` is needed, because `N` is fixed first.
- **Equivalences.** `Gamma` is R^U-satisfiable at `J` iff every `P_N` is. `J != 1` in `Gamma` iff it holds in every `P_N`. So a tracial/R^U gap of the host is exactly `J != 1` at every box together with R^U failure at some box `N_0`, and then at all larger boxes.
- **Consequence for the route.** A tiling host never supplies more than a single finite linear system with free boundary. That system is the left side of Paddock--Slofstra Proposition 5.8. Periodic structure is free for approximate models, so quantum aperiodicity is not a mechanism. The round-2 test "no periodic finite-dimensional module with `J = -I`" is necessary and carries none of the gap.
- **Model test** (calibration: a rule with nothing to separate).
  - Take one Mermin--Peres magic square per site: nine variables at each `y`, with the six row and column contexts at the same site. Formally `R = 1`, and `L_c = 4`.
  - The magic square solution group has `J != 1`: the two-qubit Pauli strategy is an exact 4-dimensional model with `J = -I`.
  - Item 4 correctly gives `J != 1` in every `P_N`. Collapsing all sites to one is a homomorphism from `P_N` onto the single-square solution group that sends `J` to `J`.
  - The same Pauli operators at every site, with `t_i = I`, give an exact model of `Gamma` with `J = -I`. So `Gamma` and every `P_N` are R^U-satisfiable, and Item 5 correctly reports no gap.

## 4. Ranked survivors and next deep lane

No uncovered survivor has leverage. Existing live routes, ranked by payoff times nearness:

1. **`hyperlinear-groups-kill-rigid-compression-defects`** (win-win).
   - If it holds, the Kun--Thom wreath, the Leavitt configuration and the Fournier-Facio group are non-hyperlinear.
   - If it fails with a Connes-embeddable counterexample, Q3.4 is answered.
   - Exact gap (`hl-hyperlinear-vs-sofic` §6): a trace-preserving model of an infinite higher-rank Kazhdan vertex, such as `EL_r(F_q[x_1..x_d])`, with a diffuse commutant summand on which a compressor acts as a proper trace-preserving endomorphism, and a vertex restriction that is not flexibly roundable.
2. **Deligne triple covers:** the central-mark HS collapse. Lane `hl-nh-deligne-extension` is running.
3. **The re-oriented LCS compiler** `perfect-completeness-constant-soundness-lcs-compiler`, after the Culf--Mastel orientation.
4. **Kervaire--Laudenbach violations over `V` or the Leavitt unit group.** Certificate search; low prior.

**Single best next deep lane.**
- Target: route 1, restricted to one question. Does a trace-preserving matrix-ultraproduct model of `EL_3(F_q[x,y,z])` exist with a diffuse commutant summand carrying a proper trace-preserving compressor endomorphism?
- A construction answers Q3.4. An obstruction proves the Kun--Thom wreath non-hyperlinear.
- Before launching, check main for running `un-*` and `kt-*` lanes on `kt-centralizer-normalization-hs`.

## 5. Checks

- Main was screened by node ids and full-text search, bounded as follows:
  - node ids: monomial / masa / normalizer / signed; mipstar / slofstra / paddock / jnvwy; kervaire / gerstenhaber; tiling / aperiodic / group-shift; burnside / exponent; factorization; entropy; strong (T); Barrington;
  - full text: coaction / Barrington; Gerstenhaber--Rothaus.
- No node on translation-invariant solution-group hosts, box localization or periodization of approximate models was found. The closest are the Labbé periodic quantum tiling nodes, which concern exact modules of SFT algebras.
- Cairn: see the lane report for the `why` result on the new claim.
