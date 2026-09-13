# An infinite simple Kazhdan group that is sofic: Part 3 of 3

Lane `ex-pestov91-harden`, 2026-09-13. It stays in this repository: publishing outside needs the user's approval.
Notation as in Parts 1–2 (`pestov-9-1-writeup-2026-09-13-part1.md`, `-part2.md`): $R = LC(X,\mathbb F_q) \rtimes
\mathbb Z$, $G = EL_3(R)$, $S = G/Z(G)$.

## 7. Consequences

**7.1 Finite simple groups converging to a simple Kazhdan group.** By Proposition 5.5 the marked groups
$PSL_{3N_k}(\mathbb F_q)$ converge to $S$. Each approximant is a marked quotient of the Kazhdan group
$EL_3(\mathbb F_q\langle t_1,\dots,t_m\rangle)$, $m = |A|+2$. The markings are the images of
$e_{ij}(1), e_{ij}(t_i), e_{ij}(\lambda)$, with $t_i \mapsto u, u^{-1}, \chi_{[x_0=a]}$. So these Cayley graphs form a
family of expanders. For the Fibonacci subshift $m = 3$ suffices, since $u$, $u^{-1}$ and $p$ generate $R$.

**7.2 $S$ is not finitely presented.** A finitely presented LEF group is residually finite: the finitely many
relators already hold in the finite model of a large ball. An infinite simple group is not residually finite.

**7.3 No factorization property.** Kirchberg's theorem, as recalled in Thom arXiv:0810.2180, Theorem 1.1: for a
Kazhdan group, the factorization property is equivalent to residual finiteness. So $S$ does not have it.

**7.4 $C^*(S)$ fails the local lifting property.** Ozawa, arXiv:math/0306067 (source lines 2190–2193): "It is
unknown whether there exists a simple property (T) group Γ which is hyperlinear. By the above theorem, the full
C*-algebra C*Γ of such a group Γ cannot have the LLP." $S$ is such a group, so $C^*(S)$ does not have the LLP.

**7.5 LEF Kazhdan groups without finite quotients.** $G$ itself is an infinite LEF Kazhdan group with no nontrivial
finite quotient (Part 2 §6.4). In this repository that refutes the general statement EKL2 of
`exact-kazhdan-radical-kernel-cannot-be-lef` (as recorded by `lef-kazhdan-group-without-finite-quotients-exists`).

**7.6 MF, but not weakly quasidiagonal.** $S$ and $G$ are MF groups that are not weakly quasidiagonal (§8).

**7.7 What the proof uses.** The argument needs four things, and any ring $R$ with them gives a simple Kazhdan LEF
group $EL_n(R)/Z$, $n \ge 3$:
- $R$ is finitely generated;
- $R$ is simple;
- $R$ embeds in an ultraproduct of matrix algebras over finite fields;
- a root-detection mechanism, here the tower subrings with absorption.

Whether different subshifts give non-isomorphic groups is not addressed.

## 8. A remark on Dadarlat's introduction

Source: M. Dadarlat, *Obstructions to matricial stability of discrete groups and almost flat K-theory*,
arXiv:2007.12655v2. The PDF pages below were read; the LaTeX source was fetched on 2026-09-13.

**Definitions** (Introduction, pp. 1–2).
- A sequence of unital maps $\varphi_n : G \to U(k_n)$ is an *asymptotic homomorphism* if (1)
  $\|\varphi_n(st) - \varphi_n(s)\varphi_n(t)\| \to 0$. It *separates* $G$ if (2) $\limsup_n\|\varphi_n(s) - 1\| > 0$
  for every $s \ne e$.
- $G$ is an *MF-group* if it has a separating asymptotic homomorphism.
- $G$ is *weakly quasidiagonal* if there is a sequence of unital completely positive definite maps
  $\varphi_n : G \to M_{k_n}$ satisfying (1) and (2). Equivalently (Definition 3.10), a ucp asymptotic homomorphism
  $C^*(G) \to M_{k_n}$ separating the points of $G$.

**The printed sentence** (p. 2): "It is clear from definitions that MF ⇒ weak quasidiagonality and matricial
stability ⇒ weak matricial stability."

**Two further statements of the paper.**
- Example 3.15(ii), p. 9: "Thom (cf. Yamashita) noted that infinite simple property (T) groups are not
  quasidiagonal, and in fact they are not weakly quasidiagonal, see Proposition 3.19."
- Proposition 3.19 (Ozawa–Thom), p. 10: "If an infinite property (T) group G is weakly quasidiagonal, then G has an
  infinite residually finite quotient."

**What $S$ shows.**
- **$S$ is MF.** LEF gives exactly multiplicative permutation models on finite sets. Their permutation matrices
  $\sigma(g)$, $g \ne 1$, move a basis vector, so $\|\sigma(g) - 1\| \ge \sqrt 2$.
- **$S$ is not weakly quasidiagonal.** $S$ is infinite, Kazhdan and simple, so its only quotients are $S$ and 1,
  and $S$ is not residually finite. By Proposition 3.19 it is not weakly quasidiagonal.

So the first clause of the printed sentence, "MF ⇒ weak quasidiagonality", fails. $G$ is a second counterexample: it
is MF and Kazhdan, with no nontrivial finite quotient.

**Proposition 3.19 is correct.** Its proof, re-read on p. 10, checks step by step.
- **Infinitely many finite-dimensional irreducibles.** Malcev's theorem gives an infinite residually finite
  quotient.
- **Finitely many.** Let $f$ be the sum of their central Kazhdan projections. Weak quasidiagonality gives a
  representation $\pi$ and finite-rank projections $p_n$ that asymptotically commute with $\pi(G)$, hence with
  $\pi(f)$. Split $p_n \approx r_n + q_n$ along $\pi(f)$. Choose a nontrivial $s$ acting trivially on the
  finite-dimensional part: one exists, otherwise $G$ would be finite. Separation at $s$ forces $q_n \ne 0$ along a
  subsequence. Lemma 3.18 then gives almost invariant vectors for $\rho\otimes\bar\rho$, where
  $\rho = (1-\pi(f))\pi$. Property (T) gives an invariant vector, so $\rho$ has a finite-dimensional
  subrepresentation. That contradicts $\rho(f) = 0$.

**The arrow that follows from the definitions** is the converse: weak quasidiagonality ⇒ MF. If $\varphi_n$ is ucp
and asymptotically multiplicative, then $\varphi_n(s^{-1}) = \varphi_n(s)^*$, and $\varphi_n(s)$ is asymptotically
unitary. Its polar parts form a unitary asymptotic homomorphism with the same separation. The second clause,
"matricial stability ⇒ weak matricial stability", is correct: polar parts plus stability give nearby genuine
representations.

**The paper's main theorems do not use the failing clause.** The Introduction derives Theorem 1.1 from Theorem 1.2.
That derivation goes through:
- a matricially stable MF group is MAP (Lemma 3.17(i));
- MAP groups are quasidiagonal (Remark 3.5(i));
- quasidiagonal groups are weakly quasidiagonal (p. 2).

None of these steps is the failing clause. Nothing else in the paper was audited.

**Internal evidence of a slip.** p. 1 prints "It is an open problem to find examples of discrete countable groups
which are not MF". Just before Proposition 3.19 the paper recalls that lattices in $Sp(n,1)$, $n \ge 2$, have
infinite simple quotients, and those are Kazhdan. With the printed arrow, such quotients would be non-MF groups,
settling that open problem. The intended arrow was presumably the converse.

**In this repository.** Every exclusion node that deduced "non-MF" from "infinite simple Kazhdan", or from "Kazhdan
without finite quotients", rested on this clause. Those routes are invalidated by
`mf-to-weak-qd-citation-has-unproved-lifting-step`, and `S` refutes their targets.

## 9. Credits

| ingredient | source | how it was checked |
|---|---|---|
| The question | Pestov, arXiv:0804.3968, Open question 9.1, p. 21; origin in Ozawa, arXiv:math/0306067 (quote in §7.4) | PDF p. 21 (earlier lanes); Ozawa e-print source, lines 2190–2193 |
| Property (T) of $EL_n(R)$, all f.g. rings | Ershov–Jaikin-Zapirain, Invent. Math. 179 (2010), arXiv:0809.4095v2, Theorem 1.1 | e-print source lines 405–410; `Theorem` counted within sections |
| Periodic approximation giving LEF | Grigorchuk–Medynets, arXiv:1105.0719, Theorem 2.6: "The topological full group of any Cantor minimal system is an LEF group." (p. 5; proof in §5 via Kakutani–Rokhlin towers) | PDF p. 5 |
| Simplicity of the ring, complex coefficients | Brown–Clark–Farthing–Sims, arXiv:1204.3127, Theorem 4.1 (`thm:alg_simple`): the complex Steinberg algebra $A(G)$ of a Hausdorff ample groupoid is simple iff $G$ is effective and minimal | e-print source; the number 4.1 is also used by Clark–Edie-Michell |
| Simplicity over any field | Clark–Edie-Michell, arXiv:1403.4684, Corollary 4.6: "$A_R(G)$ is simple if and only if $G$ is effective and minimal, and $R$ is a field"; Steinberg, arXiv:1408.6014, Corollary 3.6: "$\Bbbk\mathscr G$ is simple if and only if $\mathscr G$ is effective and minimal" ($\Bbbk$ a field, $\mathscr G$ Hausdorff ample) | PDF p. 7 and PDF p. 10 |
| Nearest earlier object | Thom, arXiv:0810.2180, Theorem 1.4: a finitely generated Kazhdan LEF group without the factorization property (not simple) | e-print source, counters |
| Kirchberg's theorem | as Thom, arXiv:0810.2180, Theorem 1.1 | e-print source |
| MF versus weak QD | Dadarlat, arXiv:2007.12655v2, p. 2, Example 3.15, Proposition 3.19 | PDF pp. 2, 9, 10 and source |
| LEF ⇒ sofic ⇒ hyperlinear | standard (Elek–Szabó; Ceccherini-Silberstein–Coornaert, Cor. 7.5.11, as cited by Grigorchuk–Medynets p. 5) | argument given in Part 2 §5.3 |

The ring $R$ is the Steinberg algebra of the transformation groupoid $X \rtimes \mathbb Z$. That groupoid is effective,
because the action is free, and minimal. So the two field-general corollaries recover Part 1 §3.3, which is proved
there directly.

**New in this development** (lane `ex-kazhdan-simple-hyperlinear`, 2026-09-12):
- $EL_3$ over the crossed-product ring of a minimal subshift;
- root detection through tower subrings and absorption;
- the resulting infinite simple Kazhdan LEF group, which answers Question 9.1.

## 10. Literature check (bounded, 2026-09-12/13)

**Earlier passes, in `ex-novelty-pestov91-deep-pass-2026-09-12.md` and Part 2 of the original artifact:**
- LaTeX greps of 12 sources, including Pestov–Kwiatkowska, Capraro–Lupini, Thom's ICM survey, EJKZ graded root
  systems, de Cornulier, and Alekseev–Thom arXiv:2608.05362, the latest expert list of known examples;
- web searches;
- titles of 369 citing works.

None names an earlier infinite simple Kazhdan group that is sofic, hyperlinear or LEF. Pestov–Kwiatkowska (2009)
still call the question open.

**This pass: OpenAlex, titles and abstracts where OpenAlex has them, keyword scan for Kazhdan/(T) together with
simple and with sofic/hyperlinear/LEF/MF/ultraproduct words.**
- Works citing:
  - Ozawa math/0306067 (141 records);
  - Pestov's guide (176);
  - Thom 0810.2180 (60);
  - Ershov–Jaikin-Zapirain (91);
  - Grigorchuk–Medynets (24);
  - Kassabov, *Universal lattices and unbounded rank expanders* (50);
  - Mimura–Sako Parts I–III (23);
  - Caprace–Rémy, *Simplicity and superrigidity of twin building lattices* (92);
  - Kassabov–Lubotzky–Nikolov, *Finite simple groups as expanders* (67).
- All 147 OpenAlex works of the author record "Masato Mimura". Most are unrelated homonyms; the group-theory papers
  are on universal lattices, fixed points, Cayley topology, and a counterexample to the Lubotzky–Weiss conjecture.
- 24 keyword searches, including "Kac-Moody" AND lattice AND sofic, and "Kac-Moody" AND hyperlinear (both
  returned no works), and kazhdan AND simple AND "locally embeddable". Seven first-pass queries hit HTTP 429 and
  were rerun.
- **Result.** No abstract states an infinite simple Kazhdan group that is sofic, hyperlinear or LEF. The only
  tier-3 keyword hit (Kazhdan and simple and approximation words) was *Spectral gap and stability for groups and
  non-local games* (2025), where "simple" means "elementary".

**LaTeX-source greps** ("simple" within two lines of Kazhdan/(T)):
- Mimura arXiv:1809.08918 builds Kazhdan groups as diagonal products of $E(n, \mathbb F_p[H/N_m])$ over finite
  group rings, aiming at residually finite groups. It remarks that those group rings are "far from simple". It
  contains no simple LEF Kazhdan group.
- Mimura–Sako arXiv:1310.4736 and Mimura–Ozawa–Sako–Suzuki arXiv:1402.5105: no passage on simple Kazhdan groups.
- No hit in: Alekseev–Finn-Sell 1608.02242, 1901.03963, 1801.10133, Nikolov–Schneider–Thom 1703.06092, and
  Fournier-Facio–Gerasimova–Spaas 2307.13155.
- Breuillard–Lubotzky 1807.03879 discusses Kazhdan mother groups of $SL_{3n}(\mathbb F_p)$ expanders, but no
  simple infinite limit.

**Kac–Moody lattices.** They are finitely presented, hence never LEF. Nothing found proves any of them sofic or
hyperlinear. The repository node `kac-moody-lattice-is-non-hyperlinear-or-llp-failure` records only a dichotomy.

**Not reached.**
- Pisier's 2020 book chapters "Property (T) and residually finite groups" and "The WEP does not imply the LLP"
  (they cite Ozawa and Thom);
- Arzhantseva's survey *Asymptotic approximations of finitely generated groups* (2014), whose abstract matches
  (T) + simple + hyperlinear;
- the arXiv API, rate-limited (HTTP 429/503);
- journal versions.

**Verdict.** Within this bound, no earlier infinite simple Kazhdan group known to be sofic, hyperlinear or LEF was
found. "First answer to Question 9.1" is well supported, but not certified by a complete survey. The two unread
survey texts above are the cheapest next check.
