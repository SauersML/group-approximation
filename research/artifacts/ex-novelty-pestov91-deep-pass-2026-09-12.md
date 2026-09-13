# Pestov 9.1: deep novelty and open-status pass (2026-09-12)

Lane `ex-novelty`, 23:15–23:50 CDT, run at the coordinator's request.

**Claim checked:** `simple-kazhdan-lef-group-from-minimal-subshift`, ESTABLISHED on main at 8b65f0932, with review
PASS at 0efeac4106. Let X be an infinite minimal subshift and put S = EL_3(LC(X,F_q) ⋊ Z)/Z(G). The claim
is that S is infinite, simple, Kazhdan and LEF.

**Method.**
- The LaTeX sources of 12 papers were fetched on MSI from `arxiv.org/e-print` (all HTTP 200). I grepped them,
  with context, for passages on simple groups, Kazhdan's property (T), soficity, hyperlinearity, LEF and open
  questions.
- The arXiv v8 PDF of Pestov's guide was read as page images, pp. 20–22.
- OpenAlex citing-work lists were read at title level: math/0306067 (138 works), 0810.2180 (58), 0804.3968 (173).

**Tags.**
- S: LaTeX source read.
- P: PDF page read.
- T: title only.

Only the passages named below were read. No citing work was read beyond its title.

## (a) The printed question

Pestov, *Hyperlinear and sofic groups: a brief guide*, arXiv:0804.3968v8 (4 Aug 2008). Its comment says it
"incorporates minor corrections made in the Bulletin of Symbolic Logic galley proofs"; the journal reference is
Bull. Symb. Logic 14 (2008) 449–480. Section 9, "Some classes of groups to look at", PDF p. 21 (P) and
`hypsof.tex` lines 843–844 (S):

> The two candidates for a counter-example are mentioned in Questions 9.1 and 9.4.
>
> **Open question 9.1** (Cf. Ozawa [64]). Let G be an infinite simple group with Kazhdan's property (T).
> Can it be hyperlinear (sofic)?

- **What it asks.** Hyperlinearity, with soficity in parentheses. It says nothing about LEF. S is LEF, hence
  sofic, so it would answer both forms.
- **Framing.** Pestov presents 9.1 as a candidate source of counterexamples, so the positive answer goes
  against his framing.
- **Journal version.** Not reached: from MSI, Project Euclid returned a 1161-byte shell page. The journal
  numbering is inferred from v8.
- **Origin.** Ozawa, *About the QWEP conjecture*, math/0306067 (S):
  - "It is unknown whether there exists a simple property (T) group Γ which is hyperlinear. By the above
    theorem, the full C*-algebra C*Γ of such a group Γ cannot have the LLP."
  - Earlier: "infinite simple groups with Kazhdan's property (T) (for existence of such groups, see [Gromov])
    do not have the property (F) as it was shown by Kirchberg".

## (b) Was such a group already known?

Within this bound, no.

- **Pestov–Kwiatkowska,** *An introduction to hyperlinear and sofic groups*, arXiv:0911.4266 (2009) (S). Right
  after the Kirchberg–Valette theorem:

  > "Ozawa asked whether every finitely generated Kazhdan group that is sofic is residually finite. A negative
  > answer was announced by Thom. Consequently, a hope to use property (T) in order to construct
  > non-hyperlinear groups is a bit diminished now, but surely not gone, as it remains in particular unknown
  > whether finitely generated simple Kazhdan group[s can be hyperlinear]"

  The line was truncated at 400 characters in my extract; the bracketed completion is a reading of the
  earlier grep line.
- **Thom,** arXiv:0810.2180 (S, P). "There are two sources of simple groups with Kazhdan's property (T)":
  Kac–Moody lattices (Caprace–Rémy) and Gromov's Tarski-monster quotients of hyperbolic Kazhdan groups.
  - His Theorem 1.4 gives a finitely generated LEF Kazhdan group without the factorization property.
  - The note never calls that group simple.
- **Capraro–Lupini,** *Introduction to sofic and hyperlinear groups and Connes' embedding conjecture*,
  arXiv:1309.2034 (S). Every "property (T)" passage is one of:
  - the definition;
  - a residually finite hyperbolic Kazhdan group K inside a sofic, non-residually-amenable group Q;
  - de Cornulier's non-Hopfian Kazhdan Γ/Z (hyperlinear, not LEA);
  - II_1 factors with property (T).

  "simple group" returns nothing.
- **Thom,** ICM survey, arXiv:1712.01052 (S). Nothing on simple Kazhdan groups. It quotes (from 1703.06092)
  "every finitely generated simple and Fin-approximated group is PSL-approximated", which is consistent with
  S being a marked limit of PSL_(3N_k)(F_q).
- **Ershov–Jaikin-Zapirain–Kassabov,** *Property (T) for groups graded by root systems*, arXiv:1102.0031 (S).
  - Simple groups appear only as finite quotients, in "The family of all finite simple groups of Lie type and
    rank ≥ 2 has a mother group with property (T)".
  - Grep for "simple ring", "sofic", "hyperlinear" and "locally embeddable" finds nothing.
- **Ershov–Jaikin-Zapirain,** arXiv:0809.4095 (S). No application to simple groups.
- **de Cornulier,** *A sofic group away from amenable groups*, arXiv:0906.3374 (S): "examples of infinite
  isolated groups with Kazhdan's Property T were given [CGP, 5.4], but it is not known if they are sofic."
- **Alekseev–Thom,** arXiv:2608.05362 (5 Aug 2026) (S). Section "Let's review some of the known examples":
  - Thom's LEF, not residually finite, not finitely presented Kazhdan group;
  - de Cornulier's finitely presentable non-Hopfian Kazhdan groups, "not known to be sofic";
  - Kar–Nikolov's finitely presented sofic non-residually-finite groups, which are not Kazhdan.

  Open problem 1: "Are there examples of finitely presented sofic groups with Kazhdan's property (T) that are
  not residually finite?" They name no simple example. This is the latest expert list of such groups found.
- **arXiv:1606.04471,** on Bowen's conjecture for sofic approximations of Kazhdan groups (S). No simple
  example.
- **Dadarlat,** arXiv:2007.12655v2 (S): "(ii) Thom (cf. Yamashita) noted that infinite simple property (T)
  groups are not quasidiagonal, and in fact they are not weakly quasidiagonal". No simple MF example.
- **Not searched.** Kac–Moody lattices beyond Cairn's dichotomy node; Mimura. The web budget was exhausted,
  and no Mimura title surfaced in the three OpenAlex lists.
- **OpenAlex (T).** No title suggests an infinite simple sofic, hyperlinear or LEF Kazhdan group. Nearest titles,
  not opened:
  - "Cohomological obstructions to lifting properties for full C*-algebras of property (T) groups" (2020);
  - "Property (T), property (F) and residual finiteness for discrete quantum groups" (2017);
  - "Flexible Hilbert–Schmidt stability versus hyperlinearity for property (T) groups" (2023);
  - "Metric ultraproducts of finite simple groups" (2014).

## A tension to state explicitly

This is not a refutation of S.

Dadarlat, arXiv:2007.12655v2, introduction (S):
- He defines an **MF group** by an asymptotic homomorphism φ_n : G → U(k_n) that separates points.
- He defines a **weakly quasidiagonal group** the same way, using unital completely positive definite maps.
- He then prints: "It is clear from definitions that MF ⇒ weak quasidiagonality and matricial stability ⇒
  weak matricial stability."

**Why it matters.** Combined with his remark (ii), that arrow would make every infinite simple Kazhdan group
non-MF, hence non-LEF. So the printed arrow contradicts S.

**Why it is probably reversed.**
- The definitions give the opposite arrow: weakly quasidiagonal ⇒ MF, by polar decomposition.
  `mf-to-weak-qd-citation-has-unproved-lifting-step` records exactly this.
- Section 3 of the same paper claims only "Quasidiagonal groups are weakly quasidiagonal".

So S stands only if the printed arrow is false for groups. ex-verify-groups checked this reading against the PDF
(0efeac4106). A public statement of S should say that it refutes that sentence of Dadarlat's introduction. A
second reader of his Section 3 is advisable.

**No conflict with other theorems.**
- **Kirchberg–Valette** (property (T) plus a subgroup of U(R) ⇒ residually finite): S lives in U(R^ω), not U(R).
- **Kirchberg:** infinite simple Kazhdan groups lack (F); so does S.
- **Ozawa:** his remark forces C*(S) to fail the LLP, as landed at da907cdf0f.
- **Alekseev–Thom:** "finitely presented ⇒ residually finite" does not apply, since S is not finitely presented.

## (c) EKL2, and LEF Kazhdan groups with no finite quotients

**What EKL2 is.** Not a literature statement. It is the general statement printed in the repository's own node
`exact-kazhdan-radical-kernel-cannot-be-lef`. `lef-kazhdan-group-without-finite-quotients-exists` quotes it as: "a
countable LEF property-(T) group with no nontrivial finite quotient is trivial".
- Main now marks it: "Correction (2026-09-12). The general statement (EKL2) below is false."
- Its deduction chain was: LEF ⇒ MF ⇒ weakly quasidiagonal (Dadarlat's printed arrow) ⇒ an infinite residually
  finite quotient (Ozawa–Thom, Dadarlat Prop. 3.19).
- The proof route was already invalidated by `mf-to-weak-qd-citation-has-unproved-lifting-step`.

**Earlier LEF Kazhdan groups without finite quotients.** None found.
- Alekseev–Thom's 2026 list names only Thom's example.
- The lane records that example as G_0(F_p[t,t^{-1}])/C. Whether it has finite quotients was not checked here.
- Every infinite simple LEF Kazhdan group has no finite quotients. So the novelty of (c) rests on the same
  search as (b).

## Verdict

- Question 9.1 is stated correctly. S answers it in both the hyperlinear and the sofic form, if the mathematics
  holds; the review passed.
- The sources above contain no earlier answer and no earlier infinite simple sofic, hyperlinear or LEF Kazhdan
  group. That includes:
  - the two post-2008 survey texts: Pestov–Kwiatkowska still calls the question open, and Capraro–Lupini is
    silent;
  - the August 2026 expert list of known examples (Alekseev–Thom).
- **Bound.**
  - 12 sources grepped, not read end to end;
  - 369 citing titles;
  - no web search, since the budget was exhausted;
  - the journal PDF was not reached;
  - Mimura and the Kac–Moody literature not searched.
- Treat "first answer to Pestov 9.1" as well supported but not certified by a full survey. State the Dadarlat
  tension alongside it.
