# sk-cornulier-q7 plan: uniform exponential growth of derived topological full groups (2026-09-13)

Lane sk-cornulier-q7 (wave 11). This is a plan artifact with no claims.

## The printed question, read at source
Cornulier, "Groupes pleins-topologiques [d'après Matui, Juschenko, Monod, …]", Séminaire Bourbaki 1064, arXiv:2002.09342. From the e-print source `bou1064.tex` l.216 (MSI copy in /scratch.global/sauer354/sk/sk-free-8/corn), section "Problèmes et questions ouvertes", item 7, verbatim:

> Le groupe $\lb\vpi\rb'$ a-t-il une croissance exponentielle uniforme? A-t-il un diamètre semi-libre (resp. sans torsion) uniforme (c'est-à-dire, existe-t-il un entier $N$ tel que pour tout système générateur, la $N$-boule contient un couple d'éléments engendrant librement un semi-groupe libre (resp. contient un élément sans torsion)?

Here φ is an infinite minimal subshift and [[φ]]′ is the derived subgroup of its topological full group. That subgroup is infinite, finitely generated and simple (Matui) and amenable (Juschenko–Monod).

## Status (bounded check)
- **Still open**, as far as this check reaches: two web searches, and the introductions of Sauer–Schesler arXiv:2605.30163 and arXiv:2606.15945, which mention neither full groups nor Cornulier.
- **Exponential growth is known:** [[φ]]′ contains a lamplighter group whenever φ is not an odometer, so for every minimal subshift.
- **Matte Bon, J. Mod. Dyn. 9 (2015), arXiv:1408.0762:** every Grigorchuk group G_ω embeds in [[φ]]′ for some minimal subshift φ.
- **Osin 2003:** elementary amenable groups of exponential growth have uniform exponential growth. [[φ]]′ is infinite, simple and amenable, so not elementary amenable, and Osin does not apply.
- **Thompson's F has uniform exponential growth** (de la Harpe). **Thompson's V does not** (Sauer–Schesler 2026).
- **Why a "no" matters:** it would give a finitely generated simple AMENABLE group of non-uniform exponential growth. Kourovka 21.117(a) is answered only by V, which is not amenable.

## Target
A minimal subshift φ with ω([[φ]]′) = 1.

**Candidate:** a primitive aperiodic substitution of constant length 2, such as period doubling or Thue–Morse.
- V_n = ζ^n(X) satisfies X = ⊔_{i<2^n} T^i V_n, and (V_n, T^{2^n}) ≅ (X, T) (Mossé recognizability; node `constant-length-substitution-tower-partition`, sk-free-8).
- So (X,T) is a tower of constant height 2^n over a copy of itself, and [[φ]] contains the level permutations Sym(2^n) and a copy of [[φ]] on every level.

**Method:** adapt Sauer–Schesler's proof for V (arXiv:2605.30163 §§2–5). V contains V_Z for every finite Z, and the rigid stabilizers of cylinders are copies of V. Their generating sets are truncated Grigorchuk level permutations plus bounded local pieces, and the counting uses inverted orbits (Bartholdi–Erschler).

**Known obstruction to a naive transfer** (sk-free-8 Attempts on `topological-full-group-derived-uniform-exponential-growth`): the local generators at one level generate a non-abelian group of exponential growth, so the per-point count explodes. This lane first reads how Sauer–Schesler count local pieces in V, then designs local generators for [[φ]]′ whose per-point groups stay small, or proves this cannot work.

## Deliverables
- Nodes on main: a theorem with proof route, or a precise obstruction; an Attempts bullet merged into the open node.
- Claims queued with sk-verify-13 (served by sk-verify-14 and 15).
- Final report to main.
