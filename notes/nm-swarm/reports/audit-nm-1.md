# audit-nm-1: fidelity audit, non-MF tex 1–1337

Lane: wave-3 audit lane, session nonsofic-existence-49 (brief `ct/ROSTER-wave3.md`).

## CLAIM

CLAIM audit of census rows graded `formalized` or `definition` for non_mf_groups_exist.tex 1–1337.
Report path only; no Lean.
- Range widened by main at 23:12 (09-13) after the coordinator restart. audit-nm-2 and audit-nm-3 are not resumed.
- audit-nm-2 left no ledger. audit-nm-3 claimed 797–1337 at 0c3336f0e but recorded no verdicts, so that range is audited here from scratch. Its file is untouched.

## Scope and method

- Census: merge 0e622f840 (21:37). The tex is unchanged since 73a84cd9c (SHA-256 0c4ada3c…, matching the census header).
  - 313 rows in range: 275 `formalized`, 38 `definition`. By section: 1–357: 42+12; 358–796: 88+13; 797–1337: 145+13.
- Root: `GroupApproximation.lean` at 4f8f90227, after wave 20 (lead-wire 7d71bbbd1, ROOT GREEN).
- Automated screens, over all 665 carriers named by these rows:
  1. **Declaration index:** built from one `git grep` over origin, and all 665 names resolve. Census `--verify-decls` agrees.
  2. **Root reachability:** the root import closure is 6861 modules. Every carrier module is in it.
  3. **Lexical scan of the 237 carrier modules:** no `sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `implemented_by` outside comments. This matters because `GroupApproximation.Meta.AxiomGuard` throws only where an `#audit_*` line names the declaration.
     - 194 carriers have `#audit_closed_axioms`.
     - 160 have `#audit_axioms`.
     - 165 theorem carriers have no audit line in their own module.
     - For the unaudited ones, closure rests on root reachability of lexically clean modules plus `scripts/Audit.lean`.
  4. **Literature inputs:** no carrier appears on an active line of `NON_MF_CENSUS_CONDITIONAL_BASELINE.txt`. The named-Prop signature scan (`…Statement/Input/Hypothesis/Package`) finds only conditional `_of_*` forms that sit beside closed siblings in the same row: `printedIntroductionAperiodicSentence_of_budget/_of_openPieces` next to `…_closed`, and `printedIntroDirectlyFiniteIffGLThreeMF_of_coreModels` next to `…_closed`.
- Reading: printed sentence versus displayed statement. Subsumption was checked wherever the carrier is more general.
  - `[D]`: I read the displayed statement of the carrier on origin. 86 rows, covering every theorem-level row and every row whose sentence carries a quantifier over rings, ranks, groups or dimensions that could be narrowed.
  - `[S]`: screened. The row passes screens 1–4, and the carrier names match the sentence's objects and step. I did not open the display. Proof-step rows of lem:two-copies, lem:rank-two, lem:ring-compression-cell, thm:transport, thm:normal-kazhdan, the proof of thm:full-defect-ring, the binary example and the proof of thm:mf-quotient-units are mostly `[S]`.

## Findings (non-PASS)

None is a FALSE-GREEN: in each case the sentence's mathematics is true and mostly already proved somewhere in the repo. Each one is a carrier that does not display the printed sentence at the printed generality or route.

1. **`d4c878a7ac22` (tex 263, thm:amenable-trace, first sentence): GENERALITY-GAP.**
   - Printed: "There is a sofic group W=W_0⋊ℤ … that is not MF", where MF is defined only for countable groups (tex 87).
   - Carrier `AmenableTraceTheorem.PrintedAmenableNonquasidiagonalTrace` binds `∃ (W K : Type) (_ : Group W) (_ : Group K) φ, … ¬ IsOperatorMF W ∧ …` and never states `Countable W`.
   - `IsOperatorMF` (`Sofic/OperatorMF.lean:89`) asks for an injective hom into `NormMatrixCoronaUnitary X`, a group of cardinality ≤ 𝔠. So the clause `¬ IsOperatorMF W` holds for every group of cardinality > 𝔠, and the display alone does not certify "not MF" in the printed sense.
   - The concrete witness `WitnessGroup` is countable. Trivial fix: a printed endpoint with `∃ (_ : Countable W)` added.
   - The same omission is in `AmenableTraceAnswersProblemX.PrintedAmenableTraceAnswersProblemX1` (row `a96c09324a87`). That row's sentence is about the trace answer, so it stays PASS.
   - Owner: map row derived from the badge (no live lane).
2. **`2a97fb901bad` (tex 284–286): ROUTE-DIFF.**
   - Printed: "Since W_0 is a direct limit of residually finite groups, it is MF [Korchagin, Cor 10 and Prop 13]". The route is RF ⇒ MF plus MF permanence under direct limits; tex 792 cites Cor 10 for RF ⇒ MF.
   - Carrier `manuscriptShiftKernelIsOperatorMF := isOperatorMF_of_isLEF (isLEF_of_locallyResiduallyFinite shiftKernel_isLocallyResiduallyFinite)` goes through locally RF ⇒ LEF ⇒ MF.
   - "Direct limit of RF groups" is not formalized, and origin has no MF direct-limit permanence theorem (`git grep 'theorem .*(directLimit|iSup|union).*MF'` is empty).
   - Proposed grade: `partial` (route difference), or keep `formalized` only by an explicit lead ruling.
   - Owner: map row (no live lane).
3. **`c890294ad9b0` (tex 253–255): GENERALITY-GAP (carrier covers one of two clauses).**
   - Printed: "Section~\ref{sec:chain-core} identifies restriction to the chain-recurrent set as the universal directly finite ring quotient, and proves that R_X is directly finite exactly when GL₃(R_X) is MF".
   - Carriers: `BilateralThree.PrintedIntroDirectlyFiniteIffGLThreeMF` (only `IsDedekindFiniteMonoid (ClopenCrossedProduct T k) ↔ IsOperatorMF GL₃`), its `_closed` and `_of_coreModels` forms, and `coreModelsLEFStatement`. None displays the universal-quotient clause.
   - Fix: add `GroupApproximation.ChainCore.ChainCoreClosures.printedCoreRingReflection_closed` (`ChainCoreClosures.lean:64`, `#audit_closed_axioms` at l.109). Its first conjunct is `IsUniversalDirectlyFiniteQuotient (coreRestrict T k)`.
   - Owner: ct-bilateral-mf (row file; regraded by ct-rank-budget).
4. **`80279f06992b` (tex 292–293): GENERALITY-GAP.**
   - Printed: "Every example above has torsion …". The examples above include `EL_n(R)` for every countable unital ring with `ts=1` and full `1−st` at every `n≥2` (tex 221–223), and `EL₄(𝒞)`, `𝒞=ℤ⟨s_0,s_1,t_0,t_1⟩/(t_is_j−δ_ij)` (tex 215–219), in every characteristic.
   - Carrier `IntroExamplesTorsion.PrintedIntroExamplesTorsion` covers `EL_n` only over rings with `(p : R) = 0`, `0 < p`, so the characteristic-0 examples are missing.
   - Fix: any nontrivial ring gives `w = e₁₂(1)e₂₁(−1)e₁₂(1) ∈ EL_n(R)`, `n ≥ 2`, with `w⁴ = 1 ≠ w`.
   - Owner: ms-intro-3.
5. **`2ff745dd7064` (tex 1060–1062, proof of cor:one-sided-ring-maximal): GENERALITY-GAP.**
   - Printed: "If R≠0 satisfies the hypothesis of Theorem~\ref{thm:full-defect-ring}, then G=EL_n(R) is countable and nontrivial, and … it is not MF", at the corollary's `n ≥ 2`.
   - Carriers `PrintedElementaryGroupNotMF` and `manuscriptElementaryGroupNotMFAllCharacteristics` quantify `∀ n, 4 ≤ n` and display no nontriviality clause. Origin has no rank-two not-MF endpoint; only `…PrimeChar` and this one.
   - Fix: a closed endpoint at `2 ≤ n` from `PrintedFullComplementaryIdempotentsRankTwo` plus `e₁₂(1) ≠ 1`.
   - Owner: audit-sec3 (row file; no live lane).

## PASS notes

- **`abfcbcb3af2b` (tex 326–332, MIP*=RE and GoldbringHart):** the carrier proves the conclusion through thm:headline, not along the printed MIP*=RE route. PASS by the lead ruling of 09-12 recorded in `cite-cstar.tsv`: the route is credit, not consumed.
- **`2d6ab84875e0` (tex 247):** `manuscriptSentence_unitGroupQuotient` takes leading inputs `(k) [Field k] [Countable k] (d) (hd : 2 ≤ d)`, carries only `#audit_axioms`, and no literature binder is present. The closed sibling `manuscriptLeavittMFQuotientFull` should be added to the row.
- **`8d0b87a46a51` (tex 106–111):** the printed corona form allows arbitrary positive `d_n`, and the cited `IsCDEOperatorMF` needs `StrictMono d`. The equivalence is `manuscriptArbitraryPositiveDimensionGroupMFDefinition` (`CurrentManuscriptDefinitionRepairs`), which should be added to the row.
- **Grade inflation, no DONE impact:** `ad33e493e32f` (proved by `Iff.rfl` from the definition), `49be74c2726c` and `469f1e197e95` are definition or setup sentences graded `formalized`; `definition` is the accurate grade.
- **`a96c09324a87`:** the TWW clause is attribution of an unused literature theorem. The mathematical clause, C*_max(W) not nuclear because W is not amenable, is carried.

## Messages

- The live-agent listing at 23:3x shows none of the owner lanes above (ct-bilateral-mf, ms-intro-3, audit-sec3) running, so they were not woken.
- The evidence and proposed rows go to ms-cite-2 (census lane, running) and to main.

## Verdicts (313 rows)

| key | tex | status | label | verdict | sentence |
|---|---|---|---|---|---|
| 3393c0cf411c | 66 | formalized | - | PASS [D] | \addtolength{\leftskip}{1.5pc}\addtolength{\rightskip}{1.5pc} Some groups are not MF\@. |
| 113e60b5f202 | 66 | formalized | - | PASS [D] | The obstruction is a property-\textup{(T)} subgroup conjugated into a proper subgroup of i… |
| e82d3011b6cb | 66 | formalized | - | PASS [D] | The unit group of the binary Leavitt algebra $L_{\F_2}(1,2)$ is a finitely generated simpl… |
| 88e8012cb87e | 87 | formalized | - | PASS [D] | A countable group $G$ is \emph{MF}~\cite{CDE} if there are positive integers $d_n$ and map… |
| 6201111b83a0 | 94 | definition | - | PASS [D] | and |
| b1b04e376fe7 | 99 | formalized | - | PASS [D] | For countable $G$, the second condition may equivalently be required along the full sequen… |
| 837b7cffa562 | 99 | formalized | - | PASS [D] | The strong convergence convention of~\cite{GaoEtAl,Schafhauser} also requires the models t… |
| 8d0b87a46a51 | 99 | formalized | - | PASS [D] | Equivalently, $G$ embeds in the unitary group of the norm matrix corona |
| be1769283b2f | 112 | definition | - | PASS [D] | Here and below, products of $C^*$-algebras mean bounded products, and $\bigoplus$ denotes … |
| d31180a98ce2 | 112 | definition | - | PASS [D] | We call a homomorphism $G\to\U(\mathcal Q_{\mathbf d})$ a \emph{corona homomorphism}. |
| ad33e493e32f | 112 | formalized | - | PASS [D] | A separable $C^*$-algebra is MF if it embeds in a norm matrix corona~\cite{BK}. |
| 10e027681ba5 | 122 | definition | - | PASS [D] | for the \emph{MF radical} of $G$. |
| f2a05ccf5990 | 122 | formalized | - | PASS [D] | For countable $G$ the quotient $G/\operatorname{Rad}_{\mathrm{MF}}(G)$ is the largest MF q… |
| 5c93c70edc4c | 126 | formalized | - | PASS [D] | Some groups admit no such approximation. |
| 651e122a919e | 134 | definition | - | PASS [D] | where $V$ is the ascending HNN extension of $\mathbb Z^3\rtimes\mathrm{SL}_3(\mathbb Z)$ a… |
| 9930600167a4 | 134 | formalized | - | PASS [D] | Every homomorphism from $W$ to an MF group kills $\varepsilon$ (Section~\ref{sec:amenable-… |
| 8766dc520cfb | 148 | formalized | - | PASS [D] | the unit group of the binary Leavitt algebra, because $H$ is simple and every homomorphism… |
| ec81a8c16b64 | 156 | definition | - | PASS [D] | We use the group commutator convention $[g,h]=ghg^{-1}h^{-1}$. |
| f355d5f61dd8 | 156 | formalized | - | PASS [D] | The groups here fail to be MF because they contain a property-\textup{(T)} subgroup that i… |
| effc40395f2b | 156 | definition | - | PASS [D] | Call $u\in G$ a \emph{compressor} of $L\le G$ when $uLu^{-1}\le L$. |
| b671ae1aab2b | 156 | formalized | - | PASS [D] | An element $c$ of the centralizer $C_G(L)$ commutes with $L$, so $ucu^{-1}$ commutes with … |
| 56d73653208a | 156 | definition | - | PASS [D] | The normal subgroup of $G$ generated by the commutators of all such elements $ucu^{-1}$ wi… |
| 51077cfd1fa7 | 177 | formalized | - | PASS [D] | since compressors, centralizing elements, and commutators of $L$ map to compressors, centr… |
| 270c3118af88 | 182 | formalized | - | PASS [D] | The criterion behind every example is Theorem~\ref{thm:compression-criterion}: for a prope… |
| a700a5798fd5 | 187 | formalized | - | PASS [S] | First, the conjugation maps $\operatorname{Ad}(V_n(g))$ of an operator norm asymptotic rep… |
| e63d12558c72 | 187 | formalized | - | PASS [S] | It compresses to a corner on which the Kazhdan projection of $K$ vanishes, and the corner,… |
| 61827aea7807 | 187 | formalized | - | PASS [D] | Its limiting trace is then the trivial character of $K$, which takes the value $1$ on that… |
| 9bab404c96c5 | 207 | formalized | - | PASS [D] | The stable letter of an ascending HNN extension of a property-\textup{(T)} group along a p… |
| 91310d39561c | 207 | definition | - | PASS [D] | For a unital ring $R$, write $e_{ij}(a)=1+aE_{ij}$ and let $\EL_n(R)$ be the subgroup of $… |
| 6b5d4b5c3081 | 207 | formalized | - | PASS [D] | A pair $s,t\in R$ with $ts=1$ gives a compressor in the same way: an explicit element $u\i… |
| 29d7a8ccf93a | 207 | formalized | - | PASS [D] | It suffices to do this once, in the universal unital associative ring $\mathcal C=\mathbb … |
| 0317786bea4d | 221 | formalized | - | PASS [D] | Theorem~\ref{thm:full-defect-ring} carries this to every countable unital ring with such a… |
| 4bf35a8f555d | 225 | definition | - | PASS [S] | Let $L_{\F_2}(1,2)$ denote the binary Leavitt algebra~\cite{Leavitt}, the unital $\F_2$-al… |
| fa08e9082236 | 234 | definition | thm:headline | PASS [D] | Let $R=L_{\F_2}(1,2)$ and let $H=R^\times$ be its unit group. |
| 63c2a4ca81c4 | 234 | formalized | thm:headline | PASS [D] | Then $H\cong\EL_4(R)$, and $H$ is nontrivial, finitely generated, and simple, and has prop… |
| 664f4f34b841 | 234 | formalized | thm:headline | PASS [D] | Every homomorphism from $H$ to an MF group is trivial. So $H$ is not MF, and $C^*_{\mathrm… |
| 0e0ede2715c4 | 243 | formalized | thm:headline | PASS [D] | For a countable purely infinite simple ring $R$ and $n\ge1$, Theorem~\ref{thm:mf-quotient-… |
| 2d6ab84875e0 | 243 | formalized | thm:headline | PASS [D] | For the unit group of $L_k(1,d)$ the quotient is $k^\times/(k^\times)^{d-1}$. |
| 307b3272f639 | 249 | definition | thm:headline | PASS [S] | For a homeomorphism $T$ of a compact metrizable zero-dimensional space $X$, let $R_X$ be t… |
| c890294ad9b0 | 249 | formalized | thm:headline | GENERALITY-GAP [D] | Section~\ref{sec:chain-core} identifies restriction to the chain-recurrent set as the univ… |
| 518c40eb5865 | 249 | formalized | thm:headline | PASS [D] | Over $\F_2$, the MF radical is exactly the locally finite restriction kernel for $\GL_n$, … |
| 58fcf9019fc9 | 249 | formalized | thm:headline | PASS [D] | If $T$ is aperiodic, the same conclusion holds already for the unit group and for every el… |
| d4c878a7ac22 | 263 | formalized | thm:amenable-trace | GENERALITY-GAP [D] | There is a sofic group $W=W_0\rtimes\mathbb Z$, with $W_0$ locally residually finite, that… |
| cd72291264e4 | 263 | formalized | thm:amenable-trace | PASS [D] | The canonical trace on $C^*_{\max}(W_0)$ is quasidiagonal, and the canonical trace on $C^*… |
| f969236a73d8 | 270 | formalized | thm:amenable-trace | PASS [D] | The group $W$ is sofic because locally residually finite groups are sofic and soficity pas… |
| a96c09324a87 | 270 | formalized | thm:amenable-trace | PASS [D] | The trace answers the question of Brown~\cite[discussion preceding Proposition~3.5.1]{Brow… |
| c4870fed3d2b | 270 | formalized | thm:amenable-trace | PASS [D] | The canonical trace of $C^*_{\max}(W_0)$ is quasidiagonal, so the crossed product by $\mat… |
| 2a97fb901bad | 270 | formalized | thm:amenable-trace | ROUTE-DIFF [D] | Since $W_0$ is a direct limit of residually finite groups, it is MF~\cite[Corollary~10 and… |
| cd3ea932e46a | 270 | formalized | thm:amenable-trace | PASS [D] | So MF groups are not closed under semidirect products with $\mathbb Z$, which answers a qu… |
| 80279f06992b | 292 | formalized | thm:amenable-trace | GENERALITY-GAP [D] | Every example above has torsion, and in the lamp construction the obstruction is itself a … |
| 6edef6dc2d68 | 310 | formalized | - | PASS [D] | A positive answer would make every countable group MF, because the reduced group $C^*$-alg… |
| abfcbcb3af2b | 310 | formalized | - | PASS [D, lead ruling 09-12] | The MF problem itself was answered negatively in 2020: the failure of the Connes embedding… |
| 4c82f6049796 | 310 | formalized | - | PASS [D] | Theorem~\ref{thm:headline} gives a counterexample among reduced group $C^*$-algebras and a… |
| 523f02126056 | 336 | formalized | - | PASS [S] | Here the rigidity comes from the Kazhdan projection of $L$ in a norm matrix corona, which … |
| a8e4ac99b640 | 364 | formalized | prop:mf-residual-calculus | PASS [S] | Every homomorphism from $G$ to an MF group is trivial on $K$ if and only if every corona h… |
| 3bd1b6ab184a | 364 | formalized | prop:mf-residual-calculus | PASS [D] | If $A$ embeds in a norm matrix corona, then $G$ is MF\@. |
| bd2989c81dc3 | 364 | formalized | prop:mf-residual-calculus | PASS [S] | In particular, this applies to the canonical group homomorphisms into $\U(C^*_{\max}(G))$ … |
| 46d40014ee9e | 376 | formalized | prop:mf-residual-calculus | PASS [S] | The image of a corona homomorphism is a countable MF group. |
| 6c597e046078 | 376 | formalized | prop:mf-residual-calculus | PASS [S] | Conversely, compose a homomorphism to an MF group with a corona embedding of its image; th… |
| bee886268f33 | 376 | formalized | prop:mf-residual-calculus | PASS [S] | If $\iota$ is an embedding as in the last assertion, then $g\mapsto\iota(\pi(g))+1-\iota(1… |
| 07de7e8a943a | 384 | formalized | prop:mf-residual-calculus | PASS [D] | For countable $G$ the quotient $G/\operatorname{Rad}_{\mathrm{MF}}(G)$ is again MF, and he… |
| 8e54f4138ac7 | 384 | formalized | prop:mf-residual-calculus | PASS [D] | This family is asymptotically multiplicative and separates every nontrivial element. |
| fd2cafafd8fa | 395 | formalized | - | PASS [S] | For an actual representation $\rho\colon G\to\U(d)$ and $u\in G$ with $uLu^{-1}\le L$, the… |
| 240357aed76a | 395 | formalized | - | PASS [S] | Property~\textup{(T)} supplies a Kazhdan projection in its place, and stable finiteness of… |
| 399d33df9009 | 405 | definition | - | PASS [S] | For $a\in M_d(\C)$ write |
| 629f562df6bc | 410 | definition | - | PASS [S] | An \emph{operator norm asymptotic representation} of a group $G$ is a sequence of maps $V_… |
| b093f3c88101 | 416 | formalized | - | PASS [S] | The elements $g$ with $\hsnorm{V_n(g)-1}\to0$ form a normal subgroup of $G$, because $\hsn… |
| db30dea6e7f0 | 425 | definition | - | PASS [S] | For $L\le G$, let |
| c9b981a3a338 | 434 | definition | - | PASS [S] | be the Hilbert--Schmidt asymptotic commutant of $V(L)$. |
| 630db09c6f46 | 434 | definition | - | PASS [S] | Coordinatewise conjugation by $V_n(g)$ defines a bijection, denoted $\operatorname{Ad}(V(g… |
| 186ab929187a | 434 | definition | - | PASS [S] | A unital $C^*$-algebra is finite if each of its isometries is unitary, and stably finite i… |
| 6b1c6779ed70 | 441 | formalized | lem:stable-finite | PASS [D] | For every sequence of positive integers $(m_n)$, the norm matrix corona |
| da52971fd39a | 445 | formalized | lem:stable-finite | PASS [D] | is stably finite. |
| a594de997cbe | 445 | formalized | lem:stable-finite | PASS [D] | Consequently, unitarily equivalent projections in a norm matrix corona are equal whenever … |
| fc6ea69c0036 | 451 | definition | lem:stable-finite | PASS [S] | Write $A$ for the displayed corona. |
| 6b308543eb28 | 451 | formalized | lem:stable-finite | PASS [S] | If $v^*v=1$ in $A$ and $(x_n)$ is a bounded lift of $v$, then $\opnorm{x_n^*x_n-1}\to0$, s… |
| daecb970c06a | 451 | formalized | lem:stable-finite | PASS [S] | So $A$ is finite, and so is $M_k(A)$, which is the corona with matrix sizes $km_n$. |
| 5e9b44d1c0bb | 451 | formalized | lem:stable-finite | PASS [S] | Finally, if $p\le q$ are equivalent projections in a finite algebra $B$ and $w$ is a parti… |
| 86ee71463acf | 463 | definition | lem:stable-finite | PASS [S] | For a group $L$ with property~\textup{(T)}, the Kazhdan projection is the central projecti… |
| 1ff4a5b717b2 | 470 | definition | lem:kazhdan-projection-order | PASS [S] | Let $P\in B$ be the image of $e_L$ under the $*$-homomorphism $C^*_{\max}(L)\to B$ induced… |
| bad6f3c843a4 | 470 | formalized | lem:kazhdan-projection-order | PASS [D] | If a unitary $U\in B$ satisfies $U\pi(L)U^*\subseteq\pi(L)$, then $U^*PU\le P$. |
| bdceff578c1b | 479 | definition | lem:kazhdan-projection-order | PASS [S] | Fix a faithful nondegenerate representation of $B$ on a Hilbert space $\mathcal H$, and le… |
| 7cf7dd61da4f | 479 | formalized | lem:kazhdan-projection-order | PASS [S] | Then $P$ is the orthogonal projection onto $\operatorname{Fix}\pi(L)$. |
| ea315c314c25 | 479 | formalized | lem:kazhdan-projection-order | PASS [S] | If $\xi\in\operatorname{Fix}\pi(L)$ and $\ell\in L$, then $\pi(\ell)U^*\xi=U^*(U\pi(\ell)U… |
| ac2c96deddba | 479 | formalized | lem:kazhdan-projection-order | PASS [S] | So $U^*\operatorname{Fix}\pi(L)\subseteq\operatorname{Fix}\pi(L)$. |
| e425c4fecaee | 479 | formalized | lem:kazhdan-projection-order | PASS [S] | Since $U^*PU$ is the orthogonal projection onto $U^*\operatorname{Fix}\pi(L)$, it follows … |
| 7229247f62b3 | 491 | formalized | thm:transport | PASS [D] | Then |
| 765fe31bdd7a | 502 | formalized | thm:transport | PASS [S] | For unitaries $A,B$, |
| a940b20e39ec | 506 | formalized | thm:transport | PASS [S] | where the norm on the left is the operator norm on the Hilbert space $(M_{d_n}(\C),\hsnorm… |
| 6bf30ab286b0 | 515 | formalized | thm:transport | PASS [D] | is a homomorphism, where $B(M_{d_n}(\C))$ denotes the operators on the Hilbert--Schmidt Hi… |
| a6985193463f | 515 | formalized | thm:transport | PASS [S] | The algebra $\mathcal B$ is a norm matrix corona with coordinate sizes $d_n^2$ after a cho… |
| 87f873612529 | 515 | formalized | thm:transport | PASS [S] | Let $P\in\mathcal B$ be the image of the Kazhdan projection of $L$~\cite{AkemannWalter} un… |
| 3df2cd0a86ce | 523 | formalized | thm:transport | PASS [S] | A Hilbert--Schmidt bounded sequence $(x_n)$ lies in $\mathcal C_2(V,L)$ if and only if |
| e702793d4e6d | 528 | formalized | thm:transport | PASS [D] | In one direction, fix $\varepsilon>0$ and, by density of the group algebra in $C^*_{\max}(… |
| ff42f7b64e53 | 534 | formalized | thm:transport | PASS [D] | where $u_\ell$ is the canonical unitary of $\ell$; the trivial character, which sends $e_L… |
| 36a9ae1219bf | 534 | formalized | thm:transport | PASS [S] | The element $\sum_{\ell\in F}a_\ell\widetilde\sigma(\ell)$ of $\mathcal B$ is within $\var… |
| a5a02a73b909 | 543 | formalized | thm:transport | PASS [S] | If $(x_n)\in\mathcal C_2(V,L)$ and $\sup_n\hsnorm{x_n}\le c$, then $\operatorname{Ad}(V_n(… |
| 35313e7f2f61 | 551 | formalized | thm:transport | PASS [S] | and $\varepsilon$ was arbitrary. |
| 734283523715 | 551 | formalized | thm:transport | PASS [S] | In the other direction, $u_\ell e_L=e_L$ in $C^*_{\max}(L)$, so $\widetilde\sigma(\ell)P=P… |
| 5c8aa0403a34 | 564 | definition | thm:transport | PASS [S] | Put $U=\widetilde\sigma(u)$. |
| fa1ec5f45603 | 564 | formalized | thm:transport | PASS [S] | Since $uLu^{-1}\le L$, $U\widetilde\sigma(L)U^*\subseteq\widetilde\sigma(L)$, so $U^*PU\le… |
| b2365e8ebb86 | 564 | formalized | thm:transport | PASS [S] | So $UP=PU$, and correspondingly $\opnorm{\operatorname{Ad}(V_n(u))P_n-P_n\operatorname{Ad}… |
| 916db87815b7 | 564 | formalized | thm:transport | PASS [S] | For $(x_n)\in\mathcal C_2(V,L)$, |
| 6869e40b6f8c | 579 | formalized | thm:transport | PASS [S] | so $\operatorname{Ad}(V(u))^{\pm1}x\in\mathcal C_2(V,L)$ by the displayed equivalence. |
| c36b6021a802 | 584 | formalized | cor:defect-hs | PASS [D] | Then |
| 310f6df94cdf | 595 | formalized | cor:defect-hs | PASS [S] | Since $c$ commutes with $L$, $(V_n(c))\in\mathcal C_2$, so $(V_n(u)V_n(c)V_n(u)^*)\in\math… |
| a6988bc68f49 | 595 | formalized | cor:defect-hs | PASS [S] | So $\hsnorm{V_n(\ell)V_n(ucu^{-1})-V_n(ucu^{-1})V_n(\ell)}\to0$, and by asymptotic multipl… |
| acc79ac4eb5f | 595 | formalized | cor:defect-hs | PASS [S] | The elements with this property form a normal subgroup of $G$, so it contains $\mathfrak D… |
| f4cdb1554874 | 608 | formalized | - | PASS [S] | Smallness in normalized Hilbert--Schmidt norm does not bound the operator norm: for |
| c9d3bf1f96b3 | 621 | formalized | - | PASS [S] | Restricting a corona homomorphism $\rho$ to a corner requires a correction: a projection $… |
| b0058fab44d8 | 628 | formalized | lem:central-corona-corner | PASS [S] | Discard the coordinates on which a fixed projection lift of \(q\) vanishes; infinitely man… |
| 4c8affbaad3c | 642 | formalized | lem:central-corona-corner | PASS [S] | Lift \(q\) to projections \(q_n\in M_{d_n}(\C)\) by functional calculus. |
| f494ded864dc | 642 | formalized | lem:central-corona-corner | PASS [S] | Since \(q\ne0\), infinitely many \(q_n\) are nonzero; retain those coordinates and put \(r… |
| 6a04faf78706 | 642 | formalized | lem:central-corona-corner | PASS [S] | Identifying each corner \(q_nM_{d_n}(\C)q_n\) with \(M_{r_n}(\C)\) identifies the corner \… |
| b0bfcbaafc1f | 642 | formalized | lem:central-corona-corner | PASS [S] | Since \(q\) commutes with \(\rho(G)\), the map \(g\mapsto q\rho(g)\) is a homomorphism fro… |
| dd524ef78e79 | 642 | formalized | lem:central-corona-corner | PASS [S] | Each value is a unitary of \(\mathcal Q_{\mathbf r}\), so, as in the proof of Lemma~\ref{l… |
| 87860427644c | 642 | formalized | lem:central-corona-corner | PASS [S] | Multiplicativity in the corona makes \((W_n)\) an operator norm asymptotic representation … |
| efed62e83cca | 659 | formalized | thm:normal-kazhdan | PASS [D] | Let \(G\) be countable and let \(K\trianglelefteq G\) have property~\textup{(T)}. |
| 7778d54e679f | 659 | formalized | thm:normal-kazhdan | PASS [S] | If every operator norm asymptotic representation \((V_n)\) of \(G\) satisfies \(\hsnorm{V_… |
| a7997fb95c84 | 668 | formalized | thm:normal-kazhdan | PASS [S] | Let \(e_K\in C^*_{\max}(K)\) be the Kazhdan projection of \(K\), and let \(p\in\mathcal Q_… |
| 9658ec21017b | 668 | formalized | thm:normal-kazhdan | PASS [S] | In any faithful representation of the corona, \(p\) is the projection onto the \(K\)-fixed… |
| 5abc59e0d8cc | 668 | formalized | thm:normal-kazhdan | PASS [S] | Since \(gKg^{-1}=K\), the range of \(\Theta(g)p\Theta(g)^*\) is \(\Theta(g)\operatorname{F… |
| 3e281c6ee4c3 | 681 | formalized | thm:normal-kazhdan | PASS [S] | and \(q=1-p\) is nonzero because \(\Theta\) is nontrivial on \(K\). |
| 2e9741292f4c | 681 | formalized | thm:normal-kazhdan | PASS [S] | By Lemma~\ref{lem:central-corona-corner} there is an operator norm asymptotic representati… |
| 0239ca7d2b5e | 681 | definition | thm:normal-kazhdan | PASS [S] | Let \(\pi\colon C^*_{\max}(K)\to\mathcal Q_{\mathbf r}\) be the homomorphism induced by \(… |
| 0c1ad4392d72 | 681 | formalized | thm:normal-kazhdan | PASS [S] | Since \(q\) commutes with \(\Theta(K)\), the map \(a\mapsto q\Theta(a)\) is a homomorphism… |
| 5c6689ae5e75 | 692 | formalized | thm:normal-kazhdan | PASS [S] | Fix a free ultrafilter \(\omega\) and let \(\tau\) be the limit along \(\omega\) of the no… |
| 00691a0fd65c | 692 | formalized | thm:normal-kazhdan | PASS [S] | A norm-null sequence has vanishing traces, since \(/\tr_{r_n}(x)/\le\opnorm x\), so \(\tau… |
| 54db830af92e | 692 | formalized | thm:normal-kazhdan | PASS [S] | The hypothesis applies to \((W_n)\) itself, so |
| 4e13d6e99e2d | 702 | formalized | thm:normal-kazhdan | PASS [S] | in the normalized Hilbert--Schmidt norm of \(M_{r_n}(\C)\), and therefore \(\tau(\pi(u_k))… |
| 377d3a03266b | 702 | formalized | thm:normal-kazhdan | PASS [S] | The trivial character \(\chi\) of \(K\) is the state of \(C^*_{\max}(K)\) with \(\chi(u_k)… |
| 82dded1b13b3 | 702 | formalized | thm:normal-kazhdan | PASS [S] | The two states \(\tau\circ\pi\) and \(\chi\) agree on every \(u_k\), hence by linearity on… |
| fb1df1a24e3f | 702 | formalized | thm:normal-kazhdan | PASS [S] | So |
| 7409ff7e2c5f | 712 | formalized | thm:normal-kazhdan | PASS [S] | a contradiction. |
| 4bc46d4603fd | 717 | formalized | thm:compression-criterion | PASS [D] | Let $G$ be countable and let $L\le G$ have property~\textup{(T)}. |
| 2f041595e7a7 | 717 | formalized | thm:compression-criterion | PASS [D] | If $K\trianglelefteq G$ has property~\textup{(T)} and $K\le\mathfrak D_G(L)$, then every h… |
| 50ca303a15db | 717 | formalized | thm:compression-criterion | PASS [D] | In particular, if such a $K$ is nontrivial, then $G$ is not MF, and if $G$ has property~\t… |
| 47c65457b63c | 729 | formalized | thm:compression-criterion | PASS [S] | By Corollary~\ref{cor:defect-hs}, every operator norm asymptotic representation of \(G\) s… |
| 4cd99c2ee1cb | 729 | formalized | thm:compression-criterion | PASS [S] | By Theorem~\ref{thm:normal-kazhdan}, every corona homomorphism is then trivial on \(K\), a… |
| 570d0f5d862a | 729 | formalized | thm:compression-criterion | PASS [S] | If \(K\ne1\), then \(G\) does not embed in an MF group, so \(G\) is not MF\@. |
| 91a29e789438 | 729 | formalized | thm:compression-criterion | PASS [S] | The last assertion is the case \(K=G=\mathfrak D_G(L)\). |
| e681972f7114 | 741 | formalized | prop:max-infinite | PASS [S] | Then $C^*_{\max}(G)$ contains a proper isometry. |
| a45c53bf93dd | 741 | formalized | prop:max-infinite | PASS [D] | In particular, $C^*_{\max}(G)$ is not stably finite, admits no faithful tracial state, and… |
| 0546c4f445c0 | 752 | definition | prop:max-infinite | PASS [S] | Let $P\in C^*_{\max}(G)$ be the image of the Kazhdan projection of $\Gamma$~\cite{AkemannW… |
| 9b21786b2a7b | 752 | formalized | prop:max-infinite | PASS [S] | Conjugation by $u$ implements the isomorphism $\Gamma\to t\Gamma t^{-1}$ on canonical unit… |
| f67f0ad4466e | 752 | formalized | prop:max-infinite | PASS [S] | The inequality is strict: in the quasi-regular representation of $G$ on $\ell^2(G/t\Gamma … |
| f6355addf8b7 | 752 | formalized | prop:max-infinite | PASS [S] | Put $q=uPu^*$, so that $P<q$, $Pq=qP=P$, $uP=qu$, and $Pu^*(1-q)=Pu^*-Pu^*uPu^*=0$, and pu… |
| 0d4f7970ddf4 | 752 | formalized | prop:max-infinite | PASS [S] | Then |
| 901f1b49e4e9 | 768 | formalized | prop:max-infinite | PASS [S] | so $s$ is a proper isometry, and $\operatorname{diag}(s,1,\ldots,1)$ is one in every matri… |
| 99f6411ca7a5 | 768 | formalized | prop:max-infinite | PASS [S] | A tracial state $\tau$ has $\tau(q-P)=\tau(s^*s)-\tau(ss^*)=0$ with $q-P$ a nonzero positi… |
| e4fcef4295ca | 768 | formalized | prop:max-infinite | PASS [D] | MF algebras are stably finite, and a separable residually finite-dimensional $C^*$-algebra… |
| f979bf757c44 | 777 | formalized | prop:max-infinite | PASS [S] | A group can satisfy the hypothesis of Proposition~\ref{prop:max-infinite} and be MF\@. |
| 07642b10d3ee | 777 | formalized | prop:max-infinite | PASS [S] | The ascending HNN extension $V$ of $\mathbb Z^3\rtimes\mathrm{SL}_3(\mathbb Z)$ along $(v,… |
| 330d435b12e2 | 792 | formalized | prop:max-infinite | PASS [S] | and reduction modulo odd integers separates its elements, so $V$ is residually finite and … |
| 7d36ccc6e758 | 792 | formalized | prop:max-infinite | PASS [S] | So the lamps of Section~\ref{sec:amenable-nonqd} are necessary for the non-MF conclusion t… |
| d269b2fd7294 | 810 | formalized | lem:two-copies | PASS [S] | Let $R$ be a unital ring with $s,t\in R$ such that $ts=1$ and $R(1-st)R=R$. |
| e123b14ddeee | 810 | formalized | lem:two-copies | PASS [S] | Then there are $v_0,v_1,w_0,w_1\in R$ with $w_iv_j=\delta_{ij}$. |
| c90393ba6292 | 810 | formalized | lem:two-copies | PASS [S] | Conversely, such elements satisfy $w_0v_0=1$ and $w_1(1-v_0w_0)v_1=1$. |
| 9dbe7e587681 | 818 | formalized | lem:two-copies | PASS [S] | Put $e=1-st$, so that $es=te=0$, and choose $a_j,b_j\in R$, $0\le j<m$, with $\sum_ja_jeb_… |
| 5870021d2e03 | 818 | definition | lem:two-copies | PASS [S] | Put |
| 91d76a509a2b | 823 | formalized | lem:two-copies | PASS [S] | For all $i,j\ge0$, $et^is^je=\delta_{ij}e$: for $j>i$ the middle factor is $s^{j-i}$, whic… |
| f437c7807b77 | 823 | formalized | lem:two-copies | PASS [S] | So $w_0v_0=t^ms^m=1$, $w_1v_1=\sum_ja_jeb_j=1$, $w_0v_1=\sum_jt^{m-j}eb_j=0$, and $w_1v_0=… |
| 0bbf89803d26 | 823 | formalized | lem:two-copies | PASS [S] | Conversely, $w_1(1-v_0w_0)v_1=w_1v_1-(w_1v_0)(w_0v_1)=1$. |
| 29f5f8b37797 | 832 | formalized | lem:rank-two | PASS [S] | Let $R$ be a unital ring and let $v,w,a,b\in R$ satisfy $wv=1$, $ba=1$, and $bv=0$. |
| a7e56a7fbc34 | 832 | formalized | lem:rank-two | PASS [S] | Then |
| 9aa5019b614f | 837 | formalized | lem:rank-two | PASS [S] | normally generates $\EL_2(R)$. |
| dbdec0d73e03 | 842 | formalized | lem:rank-two | PASS [S] | The matrix $e_{12}(v)e_{21}(b)e_{12}(-v)$ has rows $(1+vb,\,-vbv)$ and $(b,\,1-bv)$, so fo… |
| 053b6de1fe6b | 842 | definition | lem:rank-two | PASS [S] | Let $N$ be the normal closure of $D$ in $\EL_2(R)$. |
| 717152bfc217 | 842 | formalized | lem:rank-two | PASS [S] | For $r\in R$, $[D,e_{12}(ar)]=e_{12}((1+vb)ar-ar)=e_{12}(vr)$, since $ba=1$; so $e_{12}(vR… |
| 828a8cc4992b | 842 | formalized | lem:rank-two | PASS [S] | Put $f=1-vw$, an idempotent with $fv=0=wf$. |
| bd35898b630c | 842 | formalized | lem:rank-two | PASS [S] | Since $r=vwr+fr$, it remains to put $e_{12}(fR)$ in $N$, and the involution |
| 69843250783b | 853 | formalized | lem:rank-two | PASS [S] | does this by conjugation, since $zf=vf$. |
| 5e2b45529464 | 853 | formalized | lem:rank-two | PASS [S] | Put $x=vf$, $y=fw$, $q=vfw$, and $c=1-f-q$, so that $z=x+y+c$. |
| a9865697e6f3 | 853 | formalized | lem:rank-two | PASS [S] | From $wv=1$ and $fv=wf=0$: $x^2=y^2=0$, $xy=q$, $yx=f$, the idempotents $f$ and $q$ are or… |
| c97ce3c374b2 | 853 | formalized | lem:rank-two | PASS [S] | The factorization |
| db1722e32d5d | 861 | formalized | lem:rank-two | PASS [S] | puts $h=\operatorname{diag}(z,z)$ in $\EL_2(R)$, and $he_{12}(fr)h^{-1}=e_{12}(zfrz)=e_{12… |
| 05233e222ae6 | 861 | formalized | lem:rank-two | PASS [S] | So $e_{12}(r)=e_{12}(vwr)\,e_{12}(fr)\in N$ for every $r\in R$, and conjugating by $e_{12}… |
| 49be74c2726c | 869 | formalized | lem:ring-compression-cell | PASS [S] | Let $R$ be a unital ring, let $s,t\in R$ satisfy $ts=1$, and put $e=1-st$. |
| 1eb8329e0e6b | 869 | formalized | lem:ring-compression-cell | PASS [S] | In $G=\EL_4(R)$ let $L=\EL_3(R)$ occupy coordinates $1,2,3$. |
| 8f9f00fd2f55 | 869 | formalized | lem:ring-compression-cell | PASS [S] | There are $u,c\in G$ with $uLu^{-1}\le L$ and $c\in C_G(L)$ such that |
| f417d06b695f | 878 | formalized | lem:ring-compression-cell | PASS [S] | Every off-diagonal entry of a matrix in $uLu^{-1}$ has the form $sat$ with $a\in R$. |
| fa78bbc31649 | 884 | formalized | lem:ring-compression-cell | PASS [S] | Here $e^2=e$ and $es=te=0$. |
| 718cc7b04afd | 884 | formalized | lem:ring-compression-cell | PASS [S] | For $i=1,2,3$, set |
| f52624ced12a | 888 | formalized | lem:ring-compression-cell | PASS [S] | Its block on coordinates $(i,4)$ is $s&e\\0&t$, so $u=u_3u_2u_1\in\EL_4(R)$ is the matrix |
| c0383f82a141 | 900 | formalized | lem:ring-compression-cell | PASS [S] | invertible as a product of elementary matrices. |
| 8ed7601a0e35 | 900 | formalized | lem:ring-compression-cell | PASS [S] | For $1\le i\ne j\le3$ and $a\in R$, |
| 8782d1207725 | 905 | formalized | lem:ring-compression-cell | PASS [S] | both sides differ from $u$ by one entry, $sa$ in position $(i,j)$, since on the right the … |
| 3e97a39311f3 | 905 | formalized | lem:ring-compression-cell | PASS [S] | So $uLu^{-1}\le L$, and \eqref{eq:intertwine} gives the last assertion. |
| d1142160bf17 | 911 | formalized | lem:ring-compression-cell | PASS [S] | The element |
| 83ed5eb3b38c | 916 | formalized | lem:ring-compression-cell | PASS [S] | is computed in the block on coordinates $(1,4)$ using $te=0$, and a diagonal matrix of thi… |
| 0f4f9e94cc50 | 916 | formalized | lem:ring-compression-cell | PASS [S] | Both $uc$ and $e_{12}(e)u$ equal $u+et\,E_{14}$: the last column of $uc$ is $(e,et,et^2,t^… |
| 419d553a0d48 | 916 | formalized | lem:ring-compression-cell | PASS [S] | So $ucu^{-1}=e_{12}(e)$, and the Steinberg relation $[e_{12}(e),e_{23}(1)]=e_{13}(e)$ give… |
| 29118a9b250c | 931 | formalized | thm:full-defect-ring | PASS [D] | Let $R$ be a countable unital associative ring. |
| 5cbedadd4606 | 931 | formalized | thm:full-defect-ring | PASS [S] | Suppose that $s,t\in R$ satisfy |
| 7ce8c636a470 | 936 | formalized | thm:full-defect-ring | PASS [D] | that is, $1-st$ is a \emph{full} idempotent, so that $1=\sum_{j}a_j(1-st)b_j$ for finitely… |
| cede6c4edd2c | 936 | formalized | thm:full-defect-ring | PASS [D] | For every $n\ge2$, every homomorphism from $\EL_n(R)$ to an MF group is trivial. Every hom… |
| 469f1e197e95 | 948 | formalized | thm:full-defect-ring | PASS [S] | \emph{The universal group.} In $\mathcal C$ put $s=s_0$, $t=t_0$, and $e=1-st$. |
| a4cdcda5bef7 | 948 | formalized | thm:full-defect-ring | PASS [S] | Then $ts=1$, $e^2=e$, $es=te=0$, and $t_1es_1=1$. |
| a6ce75cd2625 | 948 | formalized | thm:full-defect-ring | PASS [S] | Put $G=\EL_4(\mathcal C)$ and $L=\EL_3(\mathcal C)$ on coordinates $1,2,3$. |
| 0939d33e1ff4 | 948 | formalized | thm:full-defect-ring | PASS [D] | The ring $\mathcal C$ is nonzero, since it maps onto $L_{\F_2}(1,2)$, and finitely generat… |
| ade7fe9335db | 957 | formalized | thm:full-defect-ring | PASS [S] | By Lemma~\ref{lem:ring-compression-cell} there are $u,c\in G$ with $uLu^{-1}\le L$, $c\in … |
| ec86ceff1bf1 | 963 | formalized | thm:full-defect-ring | PASS [S] | Let $N$ be the normal closure of $d$ in $G$. |
| 8227dfc88059 | 963 | formalized | thm:full-defect-ring | PASS [S] | For arbitrary $a,b\in\mathcal C$, the Steinberg relations give |
| eb7d6fe7334e | 969 | formalized | thm:full-defect-ring | PASS [S] | So $e_{42}(1)=e_{42}(t_1es_1)\in N$. |
| ad1cfff561d3 | 969 | formalized | thm:full-defect-ring | PASS [S] | Elementary signed permutation matrices conjugate this element to every off-diagonal positi… |
| 8830867a92de | 969 | formalized | thm:full-defect-ring | PASS [S] | For distinct $i,j,k$ and every $r\in\mathcal C$, |
| c0333a70aec6 | 976 | formalized | thm:full-defect-ring | PASS [S] | So $N=G$, and $\mathfrak D_G(L)=G$. |
| 2e41521883fb | 976 | formalized | thm:full-defect-ring | PASS [S] | By Theorem~\ref{thm:compression-criterion} with $K=G$, every homomorphism from $G$ to an M… |
| 45f5c651c852 | 980 | formalized | thm:full-defect-ring | PASS [S] | By Lemma~\ref{lem:two-copies} choose $v_0,v_1,w_0,w_1\in R$ with $w_iv_j=\delta_{ij}$. |
| 2d95c1b6384d | 980 | formalized | thm:full-defect-ring | PASS [S] | Then $\varphi\colon s_i\mapsto v_i$, $t_i\mapsto w_i$ is a unital ring homomorphism $\math… |
| 546f936f3fbe | 980 | formalized | thm:full-defect-ring | PASS [S] | Put |
| 53f2c41f65d9 | 989 | formalized | thm:full-defect-ring | PASS [S] | so that $T_iS_j=\delta_{ij}$, and put $p=\sum_iS_iT_i$. |
| 45c0a7a24b09 | 989 | definition | thm:full-defect-ring | PASS [S] | For a $4\times4$ matrix $A$ over $R$ put |
| 605dfb0242a3 | 994 | formalized | thm:full-defect-ring | PASS [S] | Since $(1-p)S_i=0$ and $T_j(1-p)=0$, we have $\jmath(AB)=\jmath(A)\jmath(B)$ and $\jmath(I… |
| 18ab8ca8e9ef | 1001 | formalized | thm:full-defect-ring | PASS [S] | by the computation in Lemma~\ref{lem:rank-two}, since $T_jS_i=0$. |
| e440073f849c | 1001 | formalized | thm:full-defect-ring | PASS [S] | So $\Psi(\EL_4(R))\le\EL_2(R)$. |
| 7fb55eb3f582 | 1001 | formalized | thm:full-defect-ring | PASS [S] | Let $\rho$ be a homomorphism from $\EL_2(R)$ to an MF group. |
| 16a8406515ce | 1001 | formalized | thm:full-defect-ring | PASS [S] | Composed with $\EL_4(\mathcal C)\to\EL_4(R)\to\EL_2(R)$ it is trivial, so $\rho$ kills the… |
| 1a16fdba9df3 | 1001 | formalized | thm:full-defect-ring | PASS [S] | So $\rho$ is trivial, and the image of $\EL_4(\mathcal C)$ in $\EL_2(R)$ normally generate… |
| f6edc460fb1b | 1011 | formalized | thm:full-defect-ring | PASS [S] | \emph{All ranks.} For $n\ge3$, signed permutation matrices conjugate $e_{12}(r)$ to $e_{ij… |
| 8487a62c655f | 1011 | formalized | thm:full-defect-ring | PASS [S] | A homomorphism from $\EL_n(R)$ to an MF group is trivial on that copy, hence trivial, and … |
| a4b5b1a0504a | 1020 | formalized | thm:full-defect-ring | PASS [S] | The non-MF conclusion passes up from corners: if a nonzero idempotent $p\in R$ is such tha… |
| 34366ed3b6a0 | 1020 | formalized | thm:full-defect-ring | PASS [D] | The full-defect hypothesis itself need not pass to $R$, nor need every homomorphism from $… |
| 97fcf1f9add1 | 1029 | formalized | cor:simple-infinite-ring | PASS [D] | If $R$ is a countable simple unital ring that is not directly finite, then every homomorph… |
| 017719ec2a80 | 1029 | formalized | cor:simple-infinite-ring | PASS [D] | The same conclusion holds for $R=L_k(1,m)$, for every countable field $k$ and every $m\ge2… |
| 4515e83a1b91 | 1039 | formalized | cor:simple-infinite-ring | PASS [S] | In the first case choose $ts=1\ne st$; then $1-st$ is a nonzero idempotent, and since $R$ … |
| e490d00b41a0 | 1047 | formalized | cor:simple-infinite-ring | PASS [S] | Theorem~\ref{thm:full-defect-ring} applies in both cases. |
| 18fd64bafd97 | 1051 | definition | cor:one-sided-ring-maximal | PASS [D] | Let $R$ be a countable unital ring. |
| 7b383805ef7a | 1051 | formalized | cor:one-sided-ring-maximal | PASS [D] | If $R$ is not directly finite, then $C^*_{\max}(\EL_n(R))$ contains a proper isometry for … |
| fa3d9aa8ce2c | 1051 | formalized | cor:one-sided-ring-maximal | PASS [D] | If $R\ne0$ satisfies the hypothesis of Theorem~\ref{thm:full-defect-ring}, then for every … |
| 27586e96ecfe | 1063 | formalized | cor:one-sided-ring-maximal | PASS [S] | Choose $s,t\in R$ with $ts=1\ne st$, and let $S$ be the unital subring they generate. |
| b45891d88426 | 1063 | formalized | cor:one-sided-ring-maximal | PASS [S] | Let $u$ and $L=\EL_3(S)$ be as in Lemma~\ref{lem:ring-compression-cell} for $S$; then $L$ … |
| 900689d5c4ac | 1063 | formalized | cor:one-sided-ring-maximal | PASS [S] | By Proposition~\ref{prop:max-infinite} applied to $L\le\EL_n(R)$ and $u$, $C^*_{\max}(\EL_… |
| 2ff745dd7064 | 1072 | formalized | cor:one-sided-ring-maximal | GENERALITY-GAP [D] | If $R\ne0$ satisfies the hypothesis of Theorem~\ref{thm:full-defect-ring}, then $G=\EL_n(R… |
| 518cbfd6417d | 1072 | formalized | cor:one-sided-ring-maximal | PASS [S] | The algebra $C^*_{\mathrm r}(G)$ is separable, stably finite because its canonical trace i… |
| 88cdb5eaabb4 | 1072 | formalized | cor:one-sided-ring-maximal | PASS [S] | Finally, the map $\jmath$ from the proof of Theorem~\ref{thm:full-defect-ring} is injectiv… |
| 06d71da2d355 | 1072 | formalized | cor:one-sided-ring-maximal | PASS [S] | So $R^\times$ is not MF\@. |
| 5970e738b4d9 | 1085 | formalized | prop:torsion-defect-ring | PASS [D] | Let $R$ be a countable unital ring, let $s,t\in R$ satisfy $ts=1$, and suppose that $e=1-s… |
| ed1dd8699cf4 | 1085 | formalized | prop:torsion-defect-ring | PASS [D] | Then for every $n\ge4$, |
| 7774b0de0638 | 1090 | definition | prop:torsion-defect-ring | PASS [S] | where $\EL_n(R,ReR)$ is the normal closure of the $e_{ij}(a)$ with $a\in ReR$. |
| ef7c374310ee | 1090 | formalized | prop:torsion-defect-ring | PASS [D] | In particular $\EL_n(R)$ is not MF when $e\ne0$, and if $R$ has positive characteristic, t… |
| cb0f08ae60a3 | 1096 | formalized | prop:torsion-defect-ring | PASS [S] | If $e=0$, then $ReR=0$ and $\EL_n(R,ReR)=1$, so assume $e\ne0$. |
| 057fe08fb3bb | 1096 | formalized | prop:torsion-defect-ring | PASS [S] | Let $S$ be the unital subring generated by $s,t$, and let $L=\EL_3(S)$ occupy coordinates … |
| 1538c6bcbbec | 1096 | formalized | prop:torsion-defect-ring | PASS [S] | The criterion is applied to a subgroup $B\le\EL_4(S)$ with a central element of finite ord… |
| 1246801a6fc6 | 1096 | definition | prop:torsion-defect-ring | PASS [S] | Put $f_{ij}=s^iet^j$. |
| 647f63b250b2 | 1096 | formalized | prop:torsion-defect-ring | PASS [S] | Since $es=te=0$, $f_{ij}f_{kl}=\delta_{jk}f_{il}$, so $f_{ij}^2=0$ for $i\ne j$. |
| 6efe099d7fdb | 1096 | formalized | prop:torsion-defect-ring | PASS [S] | Write $D(a)=\operatorname{diag}(1,1,1,a)$; for $i\ne j$, $D(1\pm f_{ij})=[e_{41}(f_{ii}),e… |
| 8113a9d8c968 | 1096 | formalized | prop:torsion-defect-ring | PASS [S] | Let $u$ be the compressor of Lemma~\ref{lem:ring-compression-cell}, put $w_{ij}=(1+f_{ji})… |
| 84ce319a4f15 | 1096 | formalized | prop:torsion-defect-ring | PASS [S] | Since $D(r)$ centralizes $L$, $vLv^{-1}\le L$. |
| 7eeed19cdc69 | 1096 | definition | prop:torsion-defect-ring | PASS [S] | Put |
| ee85d796d83a | 1114 | formalized | prop:torsion-defect-ring | PASS [S] | Then $c\in C_B(L)$, and from $rf_{02}r^{-1}=f_{05}$, $rf_{12}r^{-1}=f_{45}$, $f_{02}t^3=f_… |
| aeeaaeadaad3 | 1114 | formalized | prop:torsion-defect-ring | PASS [S] | So $d=[vcv^{-1},\ell]=e_{24}(-f_{02})$ lies in $\mathfrak D_B(L)$, and $[y,d]=D(1-f_{12})=… |
| bc99235426ad | 1114 | formalized | prop:torsion-defect-ring | PASS [S] | The element $z$ commutes with $L$ and $v$, and with $c$ and $y$ because $f_{12}f_{02}=f_{0… |
| 5b7bdf2351a7 | 1114 | formalized | prop:torsion-defect-ring | PASS [S] | If $me=0$ then $z^m=D(1+mf_{12})=1$, and $z\ne1$ because $tf_{12}s^2=e\ne0$. |
| 9627d330af8b | 1114 | formalized | prop:torsion-defect-ring | PASS [S] | So $\langle z\rangle$ is a nontrivial finite central subgroup of $B$ inside $\mathfrak D_B… |
| 7634d6cc067b | 1114 | formalized | prop:torsion-defect-ring | PASS [S] | Then |
| f40da910f45b | 1130 | formalized | prop:torsion-defect-ring | PASS [S] | are killed, hence every $e_{ij}(aeb)$ by the Steinberg relations and signed permutations, … |
| bbf924af98ec | 1130 | formalized | prop:torsion-defect-ring | PASS [S] | For $e\ne0$, $e_{21}(e)\ne1$. |
| 885d8e36762a | 1130 | formalized | prop:torsion-defect-ring | PASS [S] | If $R$ has characteristic $p>0$ then $pe=0$ for every such $e$, and the contrapositive giv… |
| b47d06c5c362 | 1136 | formalized | prop:torsion-defect-ring | PASS [S] | The Toeplitz--Jacobson algebra $J=\F_2\langle s,t\mid ts=1\rangle$ has $1-st\ne0$ of order… |
| 0a08ffd095d6 | 1136 | formalized | prop:torsion-defect-ring | PASS [S] | For $J$ the inclusion of Proposition~\ref{prop:torsion-defect-ring} is an equality. |
| 11137e57b26d | 1136 | formalized | prop:torsion-defect-ring | PASS [S] | The algebra $J$ acts faithfully on $V=\F_2^{(\mathbb N)}$ by the shift, $e=1-st$ is the pr… |
| 76588fb18d3b | 1136 | formalized | prop:torsion-defect-ring | PASS [S] | Let $\GL_{\mathrm{fs}}(V^n)$ be the group of automorphisms $g$ of $V^n$ such that $g-I$ ha… |
| d5e56b196927 | 1136 | formalized | prop:torsion-defect-ring | PASS [S] | The kernel of $\EL_n(J)\to\EL_n(\F_2[z,z^{-1}])$ lies in $\GL_{\mathrm{fs}}(V^n)$. |
| 7c69447e3d41 | 1136 | formalized | prop:torsion-defect-ring | PASS [S] | Over $\F_2$ every element of $\GL_{\mathrm{fs}}(V^n)$ is a product of transvections, and e… |
| 754a868fc8f5 | 1136 | formalized | prop:torsion-defect-ring | PASS [S] | So $\EL_n(J,JeJ)$ is this kernel; the quotient $\EL_n(\F_2[z,z^{-1}])$ is residually finit… |
| 6ba4fb85570c | 1159 | formalized | prop:torsion-defect-ring | PASS [S] | an infinite simple locally finite group. |
| 61b6abd03b91 | 1159 | formalized | prop:torsion-defect-ring | PASS [S] | The rank four is three plus one. |
| b6d1590be7ab | 1159 | formalized | prop:torsion-defect-ring | PASS [D] | Every countable subgroup of $\mathrm{GL}_2$ over a field has the Haagerup property~\cite[T… |
| a8ceb0650975 | 1159 | formalized | prop:torsion-defect-ring | PASS [S] | A finite subgroup $L$ of a group $G$ admits no proper compression, since $uLu^{-1}\le L$ f… |
| 3009704fef89 | 1159 | formalized | prop:torsion-defect-ring | PASS [S] | Three coordinates carry property~\textup{(T)}~\cite[Theorem~1.1]{EJZ}, and the fourth make… |
| c149d33e8f7e | 1159 | formalized | prop:torsion-defect-ring | PASS [S] | The two results are complementary: fullness gives trivial MF images at every rank $n\ge2$,… |
| 2ff180315a15 | 1177 | definition | - | PASS [S] | Put $R=L_{\F_2}(1,2)$ and $H=R^\times$. |
| 98115b8e2580 | 1177 | formalized | - | PASS [S] | By~\eqref{eq:leavitt}, the maps $x\mapsto(t_0x,t_1x)$ and $(y,z)\mapsto s_0y+s_1z$ are mut… |
| a71f65809e0b | 1184 | formalized | - | PASS [S] | The relations give $t_0s_0=1$ and $t_1(1-s_0t_0)s_1=1$, so $R$ satisfies the hypothesis of… |
| e47b80780566 | 1184 | formalized | - | PASS [S] | Since $e_{12}(1)\ne1$, the group $H$ is nontrivial. |
| 2bf4b5aca1b4 | 1192 | formalized | - | PASS [S] | The ring $R$ is purely infinite simple~\cite{AbramsAranda} and therefore an exchange ring~… |
| e4440282ed35 | 1199 | definition | - | PASS [S] | where $\EL_4(R,I)$ is the normal closure in $\EL_4(R)$ of the elementary matrices $e_{ij}(… |
| 7a20735318a1 | 1199 | formalized | - | PASS [S] | Since $R$ is simple, either $I=R$, and then $N\ge\EL_4(R)=H$, or $I=0$, and then every $g\… |
| 9085fad2968e | 1199 | formalized | - | PASS [S] | In the second case, commuting with each $e_{ij}(1)$ forces $g=\lambda I_4$ with $\lambda\i… |
| d38df1795c78 | 1199 | formalized | - | PASS [S] | So $\lambda$ lies in $Z(R)=\F_2$~\cite[Corollary~4.3]{ArandaCrow}, and $N=1$. |
| bfd4d3ceba5a | 1199 | formalized | - | PASS [S] | So $H$ is simple. |
| 8ed259b70c4a | 1199 | formalized | - | PASS [S] | It is nontrivial, and every homomorphism from it to an MF group is trivial, so $H$ is not … |
| ecb74cabf11a | 1211 | formalized | - | PASS [S] | Since $R\ne0$ satisfies the hypothesis of Theorem~\ref{thm:full-defect-ring}, Corollary~\r… |
| c0fe92a1903d | 1219 | definition | - | PASS [S] | Two idempotents $e,f$ of a ring are \emph{equivalent} if $e=xy$ and $f=yx$ for some $x,y$;… |
| 4fb6ccd3e134 | 1219 | formalized | - | PASS [S] | The algebras $L_k(1,d)$ are purely infinite simple~\cite{AbramsAranda}. |
| 8fdc908a49c7 | 1219 | definition | - | PASS [S] | Let $\GL(R)$ and $\EL(R)$ be the direct limits of $\GL_n(R)$ and $\EL_n(R)$ along $A\mapst… |
| 1f5ca4f92217 | 1219 | definition | - | PASS [S] | Write $\kappa\colon R^\times\to K_1(R)$ for the canonical map. |
| c34115be7c92 | 1233 | formalized | thm:mf-quotient-units | PASS [D] | Then every homomorphism from $\GL_n(R)$ to an MF group factors uniquely through the canoni… |
| 6b4a21de3f07 | 1233 | formalized | thm:mf-quotient-units | PASS [D] | Equivalently, $\Rad_{\mathrm{MF}}(\GL_n(R))=[\GL_n(R),\GL_n(R)]$ and $\GL_n(R)/\Rad_{\math… |
| 5c5eeda68a8a | 1244 | formalized | thm:mf-quotient-units | PASS [S] | The ring $M_n(R)$ is again countable, purely infinite, and simple~\cite[Corollary~1.7]{AGP… |
| 6c03d472e975 | 1244 | formalized | thm:mf-quotient-units | PASS [S] | Ara, Goodearl, and Pardo show that $\kappa$ is surjective with kernel $[H,H]$~\cite[Theore… |
| 55adb8bf7a88 | 1244 | formalized | thm:mf-quotient-units | PASS [S] | A countable abelian group $A$ is MF: $C^*_{\max}(A)$ is commutative and separable, hence r… |
| 23b488384d1b | 1244 | formalized | thm:mf-quotient-units | PASS [S] | So $\kappa$ is a homomorphism to an MF group, and $N\le\ker\kappa$. |
| df9b558e0cb8 | 1253 | formalized | thm:mf-quotient-units | PASS [S] | Every nonzero idempotent $e$ of $R$ is infinite~\cite[Proposition~1.5]{AGP}, so $eRe$ cont… |
| 9fcd02a03747 | 1266 | formalized | thm:mf-quotient-units | PASS [S] | since these units form the image of $\EL_m(eRe)$ under a homomorphism to $H$. |
| 64da88cf12a3 | 1274 | formalized | thm:mf-quotient-units | PASS [S] | [(a)] There are orthogonal idempotents $e_1,\dots,e_m$ with sum $1$, $m\ge4$, such that $e… |
| 49ff6f7e8ad6 | 1274 | formalized | thm:mf-quotient-units | PASS [S] | Then $R$ is the ring of $m\times m$ matrices over $T=e_1Re_1$, with identity $\operatornam… |
| 1fd773c6c314 | 1282 | formalized | thm:mf-quotient-units | PASS [S] | [(b)] For a nonzero idempotent $e$ and $n\ge2$ there are an idempotent $f<e$ equivalent to… |
| 488237f2dec0 | 1291 | formalized | thm:mf-quotient-units | PASS [S] | Let $u\in\ker\kappa$ and write $u=gvh$ as in (a). |
| 8c6a65ba3286 | 1291 | formalized | thm:mf-quotient-units | PASS [S] | The elementary matrices with $i,j\le m-1$ form $\EL_{m-1}(T)$ inside $(1-e_m)R(1-e_m)\cong… |
| 2d6574150d4d | 1299 | formalized | thm:mf-quotient-units | PASS [S] | are products of an element of $\EL_{m-1}(T)$ and a conjugate of its inverse, so they lie i… |
| f2f92d2bbb71 | 1299 | formalized | thm:mf-quotient-units | PASS [S] | Hence $u\equiv v$ modulo $N$, and $\kappa(v)=\kappa(u)=0$ because $N\le\ker\kappa$. |
| 16df92a11bc9 | 1304 | formalized | thm:mf-quotient-units | PASS [S] | By the definition of $K_1$, $\operatorname{diag}(v,1,\dots,1)\in\EL_n(R)$ for some $n\ge2$… |
| c8680722d041 | 1304 | formalized | thm:mf-quotient-units | PASS [S] | With $\theta$ and $P$ as in (b), $v=1-P+\theta(\operatorname{diag}(v,1,\dots,1))$, which l… |
| 95141daa8321 | 1304 | formalized | thm:mf-quotient-units | PASS [S] | Hence $\ker\kappa\le N$. |
| dcf6fa4be4de | 1312 | definition | cor:leavitt-mf-quotient | PASS [S] | Let $k$ be a countable field, let $d\ge2$, let $R=L_k(1,d)$, and let $H=R^\times$. |
| 6aef426dfc7a | 1312 | formalized | cor:leavitt-mf-quotient | PASS [S] | Then $H\cong\GL_d(R)$, and under this identification $\Rad_{\mathrm{MF}}(H)=[H,H]=\EL_d(R)… |
| 7916c8696def | 1321 | formalized | cor:leavitt-mf-quotient | PASS [S] | The maps $x\mapsto(t_1x,\dots,t_dx)$ and $(y_1,\dots,y_d)\mapsto\sum_is_iy_i$ are mutually… |
| 3c68c15758e8 | 1321 | formalized | cor:leavitt-mf-quotient | PASS [S] | Theorem~\ref{thm:mf-quotient-units} identifies the radical with $[H,H]$ and the quotient w… |
| 4321530b3fec | 1321 | formalized | cor:leavitt-mf-quotient | PASS [S] | Khanh--Thanh show that $\GL_d(R)=\EL_d(R)D_d(k)$, where $D_d(k)$ is the abelian group of d… |
| f6962254d259 | 1321 | formalized | cor:leavitt-mf-quotient | PASS [S] | So $[H,H]\le\EL_d(R)$, while $\EL_d(R)\le[H,H]$ because every homomorphism from $\EL_d(R)$… |
| 6d3ca647302e | 1334 | formalized | cor:leavitt-mf-quotient | PASS [D] | For $d=2$ the quotient is trivial for every countable field $k$, so every homomorphism fro… |
