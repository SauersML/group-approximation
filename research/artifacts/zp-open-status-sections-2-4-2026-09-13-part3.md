# Open status of Zaremsky's problems, Sections 2–4, part 3: literature check for Problem 4.01 (2026-09-13)

Requested by lane z4-01-amen-auto-rips. Continues parts 1 and 2 of this artifact.

## Bounds of this check

- The session's web-search budget was exhausted. Sources were fetched as arXiv abstract, HTML or PDF pages. The arXiv
  API returned HTTP 429 and 503 locally, and three API queries run from MSI returned empty responses. So there was
  **no keyword search of the arXiv corpus** for these rows: only the papers named below were read.
- The book *Word Processing in Groups* (Epstein, Cannon, Holt, Levy, Paterson, Thurston, 1992; ECHLPT) was not
  accessible. Theorem numbers from it that are not quoted by a source read here are marked **UNVERIFIED**.
- "Nothing found" means only that these fetches returned nothing.

## (1) Are amenable, solvable or polycyclic automatic groups virtually abelian?

| Item | Status | Source |
|---|---|---|
| Nilpotent automatic ⇒ virtually abelian | Known theorem | ECHLPT, Chapter 8. The theorem number is UNVERIFIED (recalled as Thm 8.2.8). Verified background: Elder–Taback, arXiv:1501.04313, §1: "As not all nilpotent groups proved to be automatic, the definition required expansion to make it more robust". The same paragraph: graph automatic but not automatic groups include "the solvable Baumslag-Solitar groups and finitely generated groups of nilpotency class 2" (citing Kharlampovich–Khoussainov–Miasnikov). |
| Automatic ⇒ quadratic Dehn function | Known theorem | Verified as quoted in Elder–Taback §1: automatic groups "are finitely presented, have word problem solvable in quadratic time and possess at most a quadratic Dehn function" [ECHLPT]. Consequence: BS(1,n) for n ≥ 2 and Sol lattices, which have exponential Dehn functions, are not automatic. |
| Biautomatic or semihyperbolic: polycyclic subgroups are virtually abelian | Believed known, UNVERIFIED | Recalled: Gersten–Short, "Rational subgroups of biautomatic groups", Ann. of Math. 134 (1991); Bridson, on subgroups of semihyperbolic groups. Not read in this check. |
| Solvable or polycyclic automatic ⇒ virtually abelian | No theorem found; no counterexample found | No keyword search was possible (see Bounds). Known non-examples are all excluded by the quadratic Dehn function bound: BS(1,n) and Sol lattices. For solvable groups with quadratic Dehn function, automaticity was not checked. |
| Amenable automatic ⇒ virtually abelian | Not a known theorem (deduction) | It would show that F is not both amenable and automatic. Zaremsky's list presents that as unknown (Problem 4.1's parenthetical), and Problems 2.1 and 2.2 are open. No counterexample is known: F is the natural candidate, and its automaticity is open. |

## (2) Finiteness properties of automatic groups, and Rips complexes

| Item | Status | Source |
|---|---|---|
| Torsion-free automatic ⇒ finite cd | Not a known theorem (deduction) | F is torsion-free with infinite cd (it contains Z^n for every n) and of type FP∞ (Elder–Taback §1, citing Brown–Geoghegan). If this implication were known, F would not be automatic, deciding Problem 2.2. But "It is not known whether Thompson's group F is automatic" (Elder–Taback, abstract, 2015; Zaremsky list 2.2, 2026). No torsion-free automatic group of infinite cd was found either. |
| Automatic ⇒ some contractible Rips complex | Not a known theorem (deduction) | For torsion-free G, a contractible R_t(G,S) carries a free, cocompact, finite-dimensional action, so its quotient is a finite K(G,1) and cd G < ∞. The same argument would decide 2.2. |
| Combings at a single scale ⇒ contractible Vietoris–Rips complexes | Known criterion | Zaremsky, "Bestvina–Brady discrete Morse theory and Vietoris–Rips complexes", arXiv:1812.10976 (v3 28 Mar 2021; Amer. J. Math.). Abstract: word-metric groups satisfying the "Link Criterion" have contractible Vietoris–Rips complexes, and the paper "provides examples using combings". The exact combing hypothesis was not read. It is the nearest single-scale combing tool to this question. |
| Combable ⇒ FP∞ | Believed known, UNVERIFIED | Recalled: J. M. Alonso, "Combings of groups", MSRI Publ. 23 (1992). Not read. |

## (3) Contractible Rips complexes of virtually abelian or crystallographic groups

| Item | Status | Source |
|---|---|---|
| Z^n × finite | Known | Li–Sánchez Saldaña, arXiv:2608.24279, Theorem 1.6: "(ℤⁿ × F, S ∪ T) is of type R" for the standard generating set S of ℤⁿ and any generating set T of a finite group F. |
| Dependence on the generating set | Unknown | Same paper: "we are not aware of a group G admitting two finite generating sets S₁ and S₂ such that (G,S₁) is of type R and (G,S₂) is not". |
| Virtually abelian with nontrivial holonomy (Klein bottle group, crystallographic groups) | Nothing found | Not among the paper's open questions (all RAAGs; the threshold for ℤⁿ; type R edge groups). |
| Groups with a proper cocompact action on a contractible complex | Open, "wide open" | Hulbert–Zaremsky, arXiv:2608.25614, Question 1.1: "Must some 𝒱ℛ_t(G) (t<∞) be contractible?" |
| ℤⁿ threshold | Conjecture | Zaremsky, arXiv:2410.11993, after Corollary 3.2: "we conjecture that 𝒱ℛ_t(ℤⁿ) is contractible for all t ≥ n". |
