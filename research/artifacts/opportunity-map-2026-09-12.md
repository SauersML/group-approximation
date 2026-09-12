# Opportunity map: uncovered high-impact targets (2026-09-12)

Strategy lane `opportunity-mapper`. This map lists open problems that:
- sit above "non-MF groups exist" and below the Millennium problems;
- are reachable with this repository's tools;
- are covered by no lane in the 2026-09-12 roster.

Nothing here is solved or attempted. The map is for assigning lanes.

**Roster checked.**
- nh-leavitt-hs-stable, nh-leavitt-hs-unstable, nh-rigid-defect-hs, q34-kt-wreath-model
- nh-kl-schur, nh-fournier-facio, nh-thompson-v, nh-mipstar-groups
- kdf-leavitt-certificate, kdf-sat, gottschalk-leavitt-ca, gottschalk-positive-host
- atiyah-nonsofic, determinant-nonsofic, hyperbolic-rf, hyperbolic-sofic, boone-higman
- bs-pc-pu, fixed-price, uct-problem, toms-winter, quasitrace

**Method.**
- **Cairn scan.** All 302 `root: true` claims on main at 6d897152 were checked against the roster.
- **Kun–Thom.** The open-question passages of arXiv:2608.06222v3 (HTML) were read. It poses nothing beyond Păunescu's question, which it answers.
- **OpenAI.** The introduction of `c1168433:official/counterexample.tex` was read.
- **Khanh.** Of arXiv:2609.08428, only the rank-two Steinberg kernel is left open (`research/artifacts/khanh-2609-08428-leavitt-gl-verified-2026-09-11.md`).
- **Other sources.** Those listed at the end.

Quotations marked *verbatim* were read on 2026-09-12 from an arXiv abstract or HTML page. Two PDF-only sources could not be text-extracted in this pass and are marked accordingly.

## Ranked shortlist

### 1. Positive Rokhlin entropy for every countable group (Seward)

- **Statement.** Every countably infinite group admits a free ergodic p.m.p. action of positive Rokhlin entropy.
- **Source** (verbatim, abstract of B. Seward, *Krieger's finite generator theorem for actions of countable groups II*, arXiv:1501.03367): "Under the assumption that every countable group admits a free ergodic action of positive Rokhlin entropy, we prove that: (i) the Rokhlin entropy of a Bernoulli shift is equal to the Shannon entropy of its base; (ii) Bernoulli shifts have completely positive Rokhlin entropy; and (iii) Gottschalk's surjunctivity conjecture and Kaplansky's direct finiteness conjecture are true."
- **Where it can fail.** Only on nonsofic groups. Verbatim, Seward arXiv:1805.08279, introduction: "The Rokhlin entropy of the Bernoulli shift G↷(L^G,λ^G) is H(L,λ) when G is sofic but when G is not sofic its value is not yet known." No nonsofic group was known before August 2026. The Leavitt unit group, the Kun–Thom groups and Fournier-Facio's group are now live test cases.
- **Why above non-MF.**
  - One statement implies two famous conjectures, Gottschalk and Kaplansky direct finiteness.
  - It also implies the entropy classification of item 2.
  - A nonsofic group with no positive-entropy free action would be the first group where entropy theory provably breaks.
- **Tool.** Hamming compression plus property (T), applied to actions:
  - `kun-thom-free-nonsofic-action`;
  - the coset Bernoulli actions (`coset-bernoulli-action-is-essentially-free`);
  - the Hilbert-hotel compression structure of the Leavitt unit groups (`hilbert-hotel-mf-absorption-theory`).
- **What does not help.** Factor maps are useless here. Verbatim, Bowen arXiv:0812.2718, abstract: "if G is a countable group that contains a nonabelian free subgroup then every pair of nontrivial Bernoulli shifts over G are weakly isomorphic".
- **First concrete step.**
  1. Read Section 1 of arXiv:1501.03367 and record the per-group form of each implication: whether the hypothesis is needed for G alone or for G and its subgroups.
  2. Test whether a strict compression `tΓt⁻¹ ⊊ Γ` over a Kazhdan pair inside `L_(F_2)(1,2)^×` constrains generating partitions of free actions, i.e. whether it forces the information of a generator to vanish.
- **Cairn root.** `every-group-has-positive-rokhlin-entropy-action`, new, landed in 6403e0ece. Its consumers are:
  - `gottschalk-surjunctivity-conjecture`;
  - the Kaplansky direct finiteness region (`leavitt-unit-group-algebra-not-directly-finite`);
  - `bernoulli-shift-entropy-classifies-for-every-group`.
  The routes should be written by the assigned lane after step 1.
- **Coordination.** It shares consumers with `gottschalk-positive-host` and `kdf-leavitt-certificate`. The target itself is uncovered.

### 2. Entropy classifies Bernoulli shifts over every countable group

- **Statement.** Let G be countably infinite, and let H(L,λ) ≠ H(K,κ). Then G↷L^G and G↷K^G are not isomorphic.
- **Source** (verbatim, Seward arXiv:1805.08279, J. Mod. Dyn. 2022, introduction):
  - "As entropy is an isomorphism invariant, it follows that G↷(L^G,λ^G) and G↷(K^G,κ^G) are non-isomorphic whenever G is sofic (so the sofic entropy is defined) and H(L,λ)≠H(K,κ)."
  - "If non-sofic countable groups G exist, then it is still unknown whether (2^G,u_2^G) and (3^G,u_3^G) are isomorphic."

  The same paper proves that equal base entropy gives isomorphic shifts over every countably infinite group. So this statement is exactly the missing half of the Kolmogorov–Ornstein classification, and it is open precisely for the groups this repository builds.
- **Why above non-MF.** It is the classification of Bernoulli shifts, a central problem of entropy theory. An isomorphism 2^G ≅ 3^G over a nonsofic group would be a landmark, and a proof would finish the classification.
- **Tool.** As in item 1.
- **Necessary features of a counterexample.**
  - By Seward's Krieger II, some countable group has no free ergodic action of positive Rokhlin entropy.
  - By arXiv:1805.08279, G itself is nonsofic.
  - By Bowen arXiv:0812.2718, the witness must be a genuine isomorphism, not a factor map.
- **First concrete step.** Record these features in Cairn. Then ask whether co-induction along a strict compression of the Leavitt unit group can change base entropy without changing the isomorphism class.
- **Cairn root.** `bernoulli-shift-entropy-classifies-for-every-group`, new, landed in 6403e0ece.

### 3. Blackadar–Kirchberg problem (STW Problem VII)

- **Statement.** Is every separable nuclear stably finite C*-algebra quasidiagonal?
- **Source.**
  - Blackadar–Kirchberg, Math. Ann. 307 (1997), Question 7.3.2.
  - Problem VII of Schafhauser–Tikuisis–White, arXiv:2506.10902.
  - Both are quoted in `stw99-problem-vii-blackadar-kirchberg`.
- **Why above non-MF.**
  - It is the nuclear form of the MF question: for nuclear algebras MF coincides with quasidiagonality.
  - The non-nuclear version already fails through MIP*=RE, as recorded in the root, so the problem is genuinely about nuclearity.
  - It is a flagship problem of the classification programme.
- **Tool.**
  - **Operator-norm compression.** This is the non-MF obstruction, and it would have to be rebuilt without property (T), because a nuclear algebra cannot contain the relevant Kazhdan group algebras.
  - **Characteristic-class obstructions.** They survive inductive limits, but so does quasidiagonality, so a counterexample must come from extensions or crossed products.
- **First concrete step.**
  - The live route `bk-counterexample-via-qd-trace-positive-class` needs `qd-nuclear-algebra-with-qd-trace-positive-singular-class`.
  - By `stw07-trace-obstruction-forces-nonqd-trace-and-non-uct`, that needs two things: a failure of the exact residual `amenable-traces-on-exact-cstar-algebras-are-quasidiagonal`, and a non-UCT nuclear quotient.
  - So the first step is to decide whether that trace residual can fail for an exact algebra built from compression data.
- **Cairn root.** Existing: `stw99-problem-vii-blackadar-kirchberg` and `blackadar-kirchberg-counterexample-exists`.
- **Caveats.**
  - The 09-11 lane `stw-bk` was dropped as below the bar. My assessment is that the problem itself is above non-MF, but the coordinator decides.
  - Its only live route runs through the UCT problem, so any lane must coordinate with `uct-problem`.

## Considered and excluded

- **Wiegold problem (Kourovka 5.52).** Solved. Verbatim, Chen–Lodha arXiv:2510.26073, abstract: "We show that any free product of nontrivial left-orderable groups has normal rank greater than one. This solves the Wiegold problem by taking free products of finitely generated perfect left-orderable groups". The remark in `l2-normal-rank-bound-fails-for-torsion-free-groups` about a road "to the Wiegold problem" predates this and should mention the solution when next edited.
- **Glebsky–Rivera: is every group weakly sofic?** High impact, and there is already a Cairn region: `glebsky-rivera-w-sofic-criterion`, `non-weakly-sofic-finitely-presented-reduction`, and `research/artifacts/non-weakly-sofic-audit-2026-08-17.md`. The tool does not reach it. `weakly-sofic-groups-can-carry-rigid-defects` records that the rigid-defect criterion fails in the weakly sofic class: finite groups with bi-invariant metrics have no Hilbert structure on which property (T) could round.
- **Cost one for infinite Kazhdan groups (Gaboriau).** Solved by Hutchcroft–Pete, *Kazhdan groups have cost 1*, arXiv:1810.11015 (title and listing only). `fpbs-kazhdan-positive-rank-gradient` then becomes a fixed-price question for profinite actions (Abért–Nikolov, arXiv:math/0701361, listing only) and belongs to `fixed-price`.
- **Aldous–Lyons conjecture.** Refuted by Bowen–Chapman–Lubotzky–Vidick and Bowen–Chapman–Vidick, as recorded in the OpenAI introduction.
- **A hyperlinear but nonsofic free action** (`hyperlinear-nonsofic-free-action`). For the Kun–Thom action this is equivalent to hyperlinearity of the wreath (`kt-free-action-hyperlinear-iff-wreath-hyperlinear`), which `q34-kt-wreath-model` covers.
- **Whitehead group vanishing for torsion-free groups** (`whitehead-vanishing-torsion-free`; Lück's survey, Conjecture 3.6). Very high impact but weak tool fit. Nothing in the compression toolkit sees K_1(ZG) of a torsion-free group, and the 08-17 audit ended in reductions only.
- **SL_3(Z) admits a nonsofic action** (`sl3z-admits-nonsofic-action`). Strong tool fit, but below the bar on its own.
- **Measure-equivalence invariance of soficity.** No source stating it as an open problem was found in this pass.

## Sources read on 2026-09-12

- B. Seward, arXiv:1501.03367 (abstract).
- B. Seward, arXiv:1805.08279 (HTML, introduction).
- L. Bowen, arXiv:0812.2718 (abstract).
- L. Chen and Y. Lodha, arXiv:2510.26073 (abstract).
- A. Kun and A. Thom, arXiv:2608.06222v3 (HTML, open questions).
- T. Hutchcroft and G. Pete, arXiv:1810.11015 (listing only).
- M. Abért and N. Nikolov, arXiv:math/0701361 (listing only).
- L. Glebsky and L. M. Rivera, arXiv:0709.0026 (abstract only; PDF text not extracted). Their criterion is already stated in `glebsky-rivera-w-sofic-criterion`.
