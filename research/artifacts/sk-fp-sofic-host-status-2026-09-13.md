# sk-fp-sofic-host: the permanence firewall for Open problem 6.1, and the status of the question (2026-09-13)

Lane sk-fp-sofic-host (wave 10). Everything here is unreviewed; review is queued with sk-verify-13.

## 0. Summary
- **New node, `lea-permanence-closure-fp-kazhdan-groups-are-residually-finite` (proof route `-proof`).**
  - Statement: every finitely presented Kazhdan group in the closure of the LEA groups under subgroups, directed unions,
    extensions with amenable quotient, graphs of groups and finite direct products is residually finite.
  - So no finitely presented Kazhdan group assembled from local amenable models by the standard soficity or
    hyperlinearity permanence theorems answers Alekseev–Thom Open problem 6.1.
- **Sharpness.** The closure under extensions with FINITE central kernel contains Deligne's triple cover `E_3` of
  `Sp_4(Z)`, which is finitely presented, Kazhdan and not residually finite. So "finite-central-by-residually-finite ⇒
  sofic" is exactly the kind of permanence theorem that would answer 6.1. It is open. Glebsky 2023 proved the weakly
  sofic version.
- **New open node, `fp-sofic-kazhdan-group-not-residually-finite` (6.1).** Three one-step routes feed it: the Deligne
  triple cover, the (2,4,6) Kac–Moody lattice, and the finitely presented simple ring route.
- **For the note's Q1 (simple groups).** A simple group has no nontrivial amenable normal subgroup, so even the missing
  permanence theorem would not produce a simple witness. The simple form needs approximations assembled by no
  permanence operation at all. That is consistent with the recorded firewalls
  (`sofic-permanence-closure-omits-simple-fa-nonsofic-groups`, `fp-simple-groups-escape-soft-hyperlinear-permanence`).
- **Note:** no change recommended (proposal artifact, one optional sentence).

## 1. Sources read at source

**Alekseev–Thom, arXiv:2608.05362** (e-print `main_final.tex`, MSI `/scratch.global/sauer354/sk/sk-fp-sofic-host/`).
- l.1732, Open problem 6.1, verbatim: "Are there examples of finitely presented sofic groups with Kazhdan's
  property~\((T)\) that are not residually finite?"
- l.1709–1724, the review, verbatim excerpts:
  - "the second author constructed a Kazhdan group which is locally embeddable into finite groups, hence sofic, but not
    residually finite";
  - "de Cornulier constructed finitely presentable non-Hopfian Kazhdan groups … Related examples are known to be
    hyperlinear by work of the second author, but they are not known to be sofic.";
  - "Kar and Nikolov constructed finitely presented sofic groups which are not residually finite. These examples do
    not have Kazhdan's property."
- Footnote at l.91: the OpenAI announcement of a nonsofic group, which "can be taken finitely presented and Kazhdan".
- de Cornulier bibitem: Proc. Amer. Math. Soc. 135 (2007), no. 4, 951–959.
- Kar–Nikolov bibitem: Proc. Math. Sci. 127 (2017), no. 2, 289–293.

**Thom, arXiv:0810.2180** (e-print `main.tex`; *Examples of hyperlinear groups without factorization property*, GGD 2010).
- Abstract, verbatim: "This group provides also an example of a sofic Kazhdan group which is not residually finite …
  We also give an example of a group which is not initially subamenable but hyperlinear."
- The section on the finitely presented example (e-print l.263–300), verbatim:
  - "We will be mainly interested in K_0(Z[1/p]). … The centre of K_0(Z[1/p]) is isomorphic to Z[1/p] and we set
    K=K_0(Z[1/p])/Z … It was shown in [de Cornulier] that K is a finitely presented non-hopfian Kazhdan group."
  - "any finitely presented initially subamenable group is residually amenable. Being a Kazhdan group, a homomorphic
    image in an amenable group follows to be finite. Hence, each finitely presented initially subamenable Kazhdan group
    is necessarily residually finite."
  - The hyperlinearity proof uses the decomposition over central characters: "The group G is hyperlinear if and only
    if the twisted group von Neumann algebra L_{β∘α}[G/C] embeds into R_ω for every character β ∈ Ĉ."

**Kar–Nikolov, arXiv:1405.1620v4** (PDF pages 1–4).
- Abstract, verbatim: "We describe elementary examples of finitely presented sofic groups which are not residually
  amenable (and thus not initially subamenable or LEA, for short)."
- Theorem 1, verbatim: "The amalgam G = SL_n(Z[1/p]) *_Z SL_n(Z[1/p]) is sofic but not LEA. In fact G does not have a
  co-amenable LEA subgroup."
- Soficity comes from amalgams over amenable subgroups (their [4], [6], [10]). The non-LEA proof uses property (T) of
  the factors.

**Glebsky, Rev. Mat. Iberoam. 39 (2023), 1097–1104, doi:10.4171/RMI/1368** (PDF pages 1–3).
- Abstract, verbatim: "we show that if in an exact sequence of groups 1 → N ↪ K ↠ G → 1 the group G is residually
  finite and N is weakly sofic, then K is weakly sofic."
- Introduction, verbatim:
  - "There is a hope that a non-sofic group may be constructed as an extension of a residually finite group by a
    finite one [1, 10]. Notice, however, that an extension of an amenable group by a sofic group is sofic [5]."
  - Here "K is an extension of G by N" means `1 → N → K → G → 1`, so the sofic case is the amenable QUOTIENT.
- About the non-approximable example of his [2]: "This example is a residually-finite-by-finite extension, it is not
  clear whether this example is a non-sofic group."

**Holt–Rees, arXiv:1601.01836** (Pacific J. Math. 287 (2017) 393–409). Search listing only, not opened: direct
products, wreath products with residually finite top group, and extensions with amenable quotient preserve
C-approximability. Not used in any proof here.

## 2. The firewall
- **Statement and proof:** the node and its route.
- **Proof in one line:** induct on the construction rank of a finite product. (T) makes amenable quotients finite
  (P3) and gives FA (P4). In the base case a finite presentation turns LEA local embeddings into amenable quotients,
  which (T) makes finite.
- **Why products are carried along:** the projections of a finitely presented Kazhdan subgroup of a product need not
  be finitely presented. The induction handles products directly instead of projecting.
- **What (T) is used for:** only (T1)–(T4) in the route: finite generation and inheritance by quotients, amenable (T)
  groups are finite, finite-index subgroups keep (T), and FA.
- **Operations deliberately excluded:**
  - **Amenable-kernel extensions.** False by Sharpness.
  - **Marked limits.** For a finitely presented group, nearby marked groups are its quotients. They are finitely
    generated Kazhdan groups but not finitely presented, and the invariant says nothing about them. So the closure
    under marked limits is not covered. For simple groups the recorded node covers it.
  - **Metric ultraproducts.** Subgroups of the universal sofic group are all sofic groups, so including them would
    turn the claim into a positive answer to the negation of 6.1.
  - **Wreath products with non-amenable top group.** Not covered unless the base is LEA. With LEA base and a
    residually finite top group the product is again LEA, by transporting supports into a finite quotient. That is
    not needed for the claim.

## 3. Map of Open problem 6.1

| Candidate | fp, (T), not RF | Soficity | Node |
|---|---|---|---|
| Deligne triple cover `E_3` of `Sp_4(Z)` | yes (finite residual `C_3`) | open; weakly sofic by Glebsky | `deligne-triple-cover-is-sofic` |
| de Cornulier's `K = K_0(Z[1/p])/Z` | yes (non-Hopfian) | open; hyperlinear by Thom | none on main |
| (2,4,6) Kac–Moody lattices `S_q`, `q ≥ 4` | yes (infinite simple) | open | `km-246-lattice-is-sofic` |
| `EL_n(R)/Z` over an fp simple ring | if the gates close | open | `sofic-fp-simple-kazhdan-group-from-fp-simple-ring` |
| arithmetic defect-saturated quotient `Q` | yes | open | `arithmetic-defect-saturated-kazhdan-group-is-sofic` |

- The first two candidates are central extensions of residually finite groups by amenable groups (`C_3`, and a group
  containing the Prüfer group `Z[1/p]/Z`).
- Only the last three would also bear on the note's Q1, and only the Kac–Moody and ring candidates are simple.
- The hyperlinear form of 6.1 is answered by Thom's `K`, through the central-character decomposition. That
  decomposition has no permutation analogue on record.

## 4. Search bounds
- **Web searches (2):**
  - "sofic groups extension amenable normal subgroup sofic quotient open problem amenable-by-sofic";
  - "Holt Rees Some closure results for C-approximable groups extensions sofic".
- **Web search for Kar–Nikolov:** one query.
- **arXiv API on MSI:** six queries returned empty results. The API is likely blocked or throttled, so nothing was
  concluded from them.
- **Sources opened:** the four e-prints and PDFs above.
- **Not found:** a claim that finite-central-by-residually-finite groups are sofic, or that 6.1 is answered. This is
  not a complete literature verification.

## 5. Sharpest next target
A permutation analogue of Thom's central-character decomposition for `E_3`: sofic models of `Sp_4(Z)` twisted by the
Deligne multiplier with vanishing defect. The repository already records the exact linear and unitary reformulations:
- `deligne-cover-linear-soficity-is-rank-projective-approximation`;
- `deligne-sector-gap-is-exactly-nonhyperlinearity`;
- the monomial and cosystole floors.

It is one lane at most, and it is owned by the w4-deligne line, not this lane.
