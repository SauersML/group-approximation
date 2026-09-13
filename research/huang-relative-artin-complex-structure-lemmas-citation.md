---
rg: 2
id: huang-relative-artin-complex-structure-lemmas-citation
kind: route
title: Import Huang's structural lemmas on relative Artin complexes
target: huang-relative-artin-complex-structure-lemmas
requires: []
---

Citation import, not a reproof. Read on 2026-09-13 from the arXiv LaTeX source of J. Huang and
P. Przytycki, arXiv:2509.06914, section "Relative Artin complexes and related background",
which restates results of J. Huang, arXiv:2305.16847 (Invent. Math. 238 (2024)). Verbatim:

1. Lemma `lem:sc` [huang2023labeled, Lem 6.2; cumplido2020parabolic, Lem 4]: "If |Λ'| ≥ 3,
   then Δ_{Λ,Λ'} is simply connected (in particular, it is connected)."
2. Lemma `lem:link` [huang2023labeled, Lem 6.4(1)]: "Let v∈Δ'=Δ_{Λ,Λ'} be a vertex of type ŝ.
   Then there is a type-preserving isomorphism between lk(v,Δ') and Δ_{Λ∖{s},Λ'∖{s}}." The
   join statement: proof of Theorem `thm:4`, "If Λ has multiple connected components, then the
   associated Artin complex is a join of several smaller Artin complexes, one for each connected
   component of Λ."
3. Lemma `lem:poset structure` [huang2023labeled, Lem 6.6]: "Suppose that Λ'=s_1⋯s_n is an
   admissible linear subgraph of a Coxeter diagram Λ. Let Δ' be the (Λ,Λ')-relative Artin
   complex, with the relation < on its vertex set induced from s_1<⋯<s_n or s_n<⋯<s_1. Then
   (Δ'^0,<) is a weakly graded poset." Definition `def:admissible`: "An induced subdiagram Λ'
   of Λ is admissible if for any vertex x of Λ', if the vertices x_1,x_2 of Λ' are in distinct
   connected components of Λ'∖{x}, then they are in distinct connected components of Λ∖{x}."
4. Theorem `thm:4cycle` [huang2023labeled, Thm 8.1]: "Let Λ be irreducible spherical, and let
   Λ'⊂Λ be a linear subdiagram. Then Δ_{Λ,Λ'} is bowtie free."

5. Remark `rem:easygirth`: "By [AS, Lem 6], if Λ is an edge labelled by m, then Δ_Λ has girth
   ≥ 2m." ([AS] is Appel–Schupp; not read.)
6. Lemma `lem:posets` [brady2010braids, Prop 1.5; haettel2023new, Prop 2.4]: "If P is a bowtie
   free weakly graded poset, then any subset Q⊂P with an upper bound has the join, and any
   Q⊂P with a lower bound has the meet."

Taking `Λ' = Λ` in 3 is allowed: `Λ` is admissible in itself. The Artin complex is flag by
[godelle2012k, Prop 4.5], as recorded in the preliminaries of arXiv:2509.06914.
