# Priority check for the relaunched lanes, 2026-09-12

Scout lane `lit-scout`, 2026-09-12 (morning CDT). Question for every running lane: has
its named problem been publicly solved, so that our work would duplicate someone else's
or lose priority? This session had already found such a case: Toms, arXiv:2609.09535,
answered STW Problem LIX in public after our internal answer.

## Sources scanned

* arXiv listings, titles filtered by the lanes' keywords:
  * math.GR recent (2609.02945 through 2609.11880) and the full math.GR August 2026 list;
  * math.OA recent (2609.03637 through 2609.11834) and the full math.OA August 2026 list;
  * math.PR recent and the full math.PR August 2026 list;
  * math.DS recent.
* Targeted web searches for each lane's problem, restricted to 2026.
* OpenAI's ten advances, from the README of `openai/ten-proofs` (fetched with `gh api`).
  The ten are:
  * sphere-packing bounds;
  * binary and spherical codes;
  * non-sofic groups;
  * Connes' rigidity conjecture;
  * permanent circuit lower bounds;
  * quantum parallel repetition;
  * CVP hardness;
  * Ehrhart's volume conjecture;
  * multicolor triangle Ramsey numbers (Erdős 183);
  * extremal compactness and degeneracy (Erdős 146, 180).

  None of these is a lane target.

Limits:
* Listing coverage is the arXiv "recent" window plus August 2026. Earlier months were
  not systematically re-scanned; earlier scouts covered August in part (see the
  `nonhyperlinear-literature-delta-*` artifacts).
* Web search is not exhaustive.
* Leads below were read at abstract level only. None is imported into the graph.

## Verdict per lane

No public solution was found for any lane's named problem as of 2026-09-12.

| Lane(s) | Problem | Public status found | Notes |
|---|---|---|---|
| nh-leavitt-hs-stable, nh-leavitt-hs-unstable | Non-hyperlinear group; normalized-HS stability of `L_(F_2)(1,2)^x` | open | Dogon arXiv:2211.10492 and arXiv:2506.20843 already in Cairn. Manzoor arXiv:2502.06697 is about IRSs and equivalence relations, not groups; already in Cairn. |
| nh-rigid-defect-hs, q34-kt-wreath-model | Hyperlinear rigid defects; Pestov Q3.4 | open | Alekseev–Thom arXiv:2608.05362 (sofic centralizers of Kazhdan groups) already in Cairn. |
| nh-kl-schur | Kervaire–Laudenbach | open | Two leads, below. |
| nh-fournier-facio | Hyperlinearity of the torsion-free nonsofic group (arXiv:2608.02025) | open | — |
| nh-thompson-v | Soficity and hyperlinearity of Thompson's V | open | The August math.GR titles on T and F (arXiv:2608.16530, 2608.17193) do not bear on it. |
| kdf-leavitt-certificate, gottschalk-leavitt-ca, gottschalk-positive-host | Kaplansky direct finiteness; Gottschalk surjunctivity | open | Bowen–Chapman arXiv:2511.06586 already in Cairn. |
| atiyah-nonsofic, determinant-nonsofic | Strong Atiyah and Lück determinant counterexamples | open | — |
| hyperbolic-rf, hyperbolic-sofic | Residual finiteness and soficity of hyperbolic groups | open | Hill arXiv:2609.07639 (RF of inverse images of non-uniform SU(2,1) lattices in covers) is not about hyperbolic groups. |
| boone-higman | Boone–Higman conjecture | open in general | The hyperbolic case (arXiv:2309.06224, Duke 2026) is already in Cairn. |
| bs-pc-pu | `p_c < p_u` for nonamenable transitive graphs | open | Hartarsky–Severo–Teixeira arXiv:2609.07768 already in Cairn. Tran–Nguyen arXiv:2609.07026 ("Locality of Bernoulli site percolation on transitive graphs") not read. |
| fixed-price | Gaboriau's fixed price problem | open | Donoso-Echenique–Silva arXiv:2608.20472 has group cost 1 for `B(m,n)` at large odd `n`; per the abstract this is the infimum, not fixed price. Slutsky arXiv:2607.20273. Both already in Cairn. |
| uct-problem | UCT problem | open | Bunke–Duenzinger arXiv:2609.04795 (products in KK- and E-theory) does not address it. |
| toms-winter | Toms–Winter, strict comparison implies Z-stability | open | Bell arXiv:2609.10653 (`C*_r((Z/2) wr Gamma)` not pure) concerns nonsimple algebras, so it is not a counterexample. |
| quasitrace | Are bounded 2-quasitraces traces? | open | Gow arXiv:2601.04431v2 already in Cairn. Lead below. |

Outside the lanes, not threats: Houdayer–Marrakchi arXiv:2609.11462 (classification of
flows on II_1 factors and Connes' bicentralizer problem), and Ozawa arXiv:2609.08892
(already in Cairn).

## Leads forwarded (abstract level, not imported)

* **To `quasitrace`.** Arulseelan–Hanson, arXiv:2609.10218v1 (9 Sep 2026), "Every
  AW*-Algebra is Normal".
  * Resolves Wright's normality question.
  * Forcing transfer: a ZFC proof that all AW*-factors are monotone complete yields one
    for all AW*-algebras.
  * The abstract does not mention quasitraces. It is relevant only through Gow's
    equivalence.
* **To `nh-kl-schur`.** Two leads.
  * Alekseev–Schneider, arXiv:2609.09058v1 (8 Sep 2026), "Images of word maps with
    constants on algebraic groups". For quasisimple `G(L)` over a local field and
    `w in (G*F_r)\G`, either `w` has a Tomanov-small critical constant, or
    `dim w(G^r) >= c(G) > 1`.
  * Klyachko–Mikheenko–Olshanskii, arXiv:2608.28045v2, "Solvability of unimodular
    equations in groups and Lie algebras". This is in-group solvability for finitely
    generated solvable groups, so it is weak for KL.
* **To `nh-leavitt-hs-stable` and `nh-rigid-defect-hs`.** Lubotzky–Yao,
  arXiv:2608.03561v2 (31 Aug 2026), "Non Uniform Kazhdan Constant for Linear Groups". No
  infinite finitely generated linear group is uniformly Kazhdan. So any rounding or
  normalization step that needs a Kazhdan constant uniform over generating sets fails for
  the linear Kun–Thom Theorem E pairs. It says nothing about `L^x`, which is not known to
  be linear.

Any lane that uses a lead must read the PDF first (extraction through msi) and import it
through a `-citation` route with verbatim statements.
