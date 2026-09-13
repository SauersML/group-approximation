# Zaremsky Problem 1.20: status, reformulation and firewalls (2026-09-13)

Lane `z1-20-simple-fp2`. Root: `zaremsky-1-20-uncountably-many-simple-fp2-groups`.

## 1. The problem

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026), Section 1, Problem 20, verbatim:
"(Added 6/12/25) Are there uncountably many simple groups of type FP2? Of type FP?"

Reading: isomorphism types; type FP_2 and FP over `Z`. Since there are countably many finitely presented groups,
a positive answer needs simple groups of type FP_2 that are not finitely presented, for all but countably many
members of the family. Type FP forces finite cohomological dimension, so simple groups of type FP are torsion-free.

## 2. Literature checked

**Leary, "Uncountably many groups of type FP", arXiv:1512.06609v4 (Proc. London Math. Soc. 2018).** Read from the
arXiv PDF, pages 1–4 and 31–35.
- Definition 1.1: for a finite connected flag complex `L`, a finite set `Γ` of directed edge loops normally
  generating `π_1(L)`, and `0 ∈ S ⊆ Z`, the presentation `P_L(Γ, S)` has the directed edges of `L` as generators,
  edge relations `a ā = 1`, triangle relations `abc = 1` and `a^{-1} b^{-1} c^{-1} = 1`, and long cycle relations
  `a_1^n a_2^n ⋯ a_l^n = 1` for `n ∈ S − {0}` and `(a_1, ..., a_l) ∈ Γ`.
- Theorem 1.2 (`L` not simply connected): (1) there are uncountably many (in fact `2^ℵ0`) isomorphism types of
  `G_L(S)`; (2) for `0 ∈ S`, `P_L(Γ, S)` presents `G_L(S)`; (3) `G_L(S)` is finitely presentable iff `S` is
  finite; (4) `G_L(S)` embeds in a finitely presented group iff `S` is recursively enumerable.
- Functoriality (p. 2): for `S ⊆ T` there is a natural surjection `G_L(S) -> G_L(T)`; `G_L(Z) = BB_L` and
  `G_L(∅) ≅ BB_{L̃} ⋊ π_1(L)`.
- Theorem 1.3: `L` and `L̃` are `R`-acyclic iff every `G_L(S)` is of type FH(R), iff every `G_L(S)` is of type
  FP(R); similarly for FP_n with `(n−1)`-acyclicity.
- Theorem 19.2: "In the case when π_1(L) is perfect, d(C_2^l) ≤ d(C_2^t). Hence in this case G_L(S) is type
  FP_2(Z)." This is the relation-module form of the perfect-kernel mechanism.
- Section 21 names as open: does every group of type F_n embed in a group of type F_{n+1}? Does every group of
  type FP_n(R) embed in a group of type FP_{n+1}(R)? The case n = 1 of the second question is done in Leary,
  arXiv:1610.05813: every countable group embeds in a group of type FP_2(Z).
- None of the `G_L(S)` is simple: each surjects onto `BB_L`, which is infinite and residually finite.

**Llosa Isenrich–Schesler–Wu, "Infinitely presented simple groups separated by homological finiteness properties",
arXiv:2510.01952v1 (2 October 2025).**
- Abstract (verbatim from the arXiv abstract page): "Given a finitely generated linear group G over ℚ, we
  construct a simple group Γ that has the same finiteness properties as G and admits G as a quasi-retract. As an
  application, we construct a simple group of type FP∞ that is not finitely presented. Moreover we show that for
  every n ∈ ℕ there is a simple group of type FP_n that is neither finitely presented nor of type FP_{n+1}.
  Since our simple groups arise as Röver–Nekrashevych groups, this answers a question of Zaremsky."
- The following was read through the arXiv HTML page with a summarizing fetch tool. Exact wording should be
  re-read before any citation route uses it.
  - Theorem 1.1: simple groups `G_Γ` from finite graphs `Γ` with the finiteness properties of `BB_Γ`.
  - Theorem 1.4: every finitely generated `H ≤ GL_n(Q)` lies in a simple group with the same finiteness
    properties that quasi-retracts onto `H`.
  - Construction: `G = [V_m(j(Γ)), V_m(j(Γ))]`, the commutator subgroup of a Röver–Nekrashevych group of a
    self-similar group `j(Γ)`; simplicity from Nekrashevych.
  - Proposition 3.1: `V_d(G)` inherits type FP_n(R) from `G`.
  - Question 1.12: does every countable group embed in a simple group of type FP_2(Z)? This is Zaremsky's
    Problem 1.25.
- Consequences for Problem 1.20: countably many groups (countable inputs); torsion present (they contain
  Higman–Thompson groups), so none is of type FP.

**Related, not simple.**
- Kropholler–Leary–Soroko, arXiv:1712.05826: uncountably many quasi-isometry classes of groups of type FP.
- Li–Sánchez Saldaña, arXiv:2502.14751, abstract: "for n≥2, we deduce the existence of uncountably many
  quasi-isometry classes of one-ended groups that are of type FP_n and not of type FP_{n+1}."

**Search bound.**
- A few web searches, then the session's search budget ran out.
- arXiv listing searches: "simple groups of type FP" (no results), "almost finitely presented" with "simple" (no
  results), "uncountably many simple groups" (nothing relevant through arXiv:2608.30881).
- MathSciNet and zbMATH were not reached.
- No answer to Problem 1.20 was found. The list kept it open on July 12, 2026, when it added Problem 1.25 citing
  Llosa Isenrich–Schesler–Wu.

## 3. Established tools (landed with proofs)

1. `fp2-iff-quotient-of-fp-group-by-perfect-normal-subgroup`: `G` is FP_2 iff `G = H/N` with `H` finitely
   presented and `N` perfect. Quotients of FP_2 groups by perfect normal subgroups are FP_2, and normal closures
   of perfect subgroups are perfect.
2. `simple-fp2-uncountability-via-perfect-simple-quotients`: part (i) of Problem 1.20 holds iff some finitely
   presented `H` has uncountably many perfect normal subgroups with simple quotient.
3. `rover-nekrashevych-groups-have-co-re-word-problem` and `fg-groups-with-re-or-co-re-word-problem-are-countable`:
   finite-data self-similar and Röver–Nekrashevych constructions give countably many groups. In any witnessing
   family, all but countably many members have word problem neither r.e. nor co-r.e.

## 4. Firewalls (where natural approaches die)

- **Röver–Nekrashevych / self-similar inputs** (the Llosa Isenrich–Schesler–Wu machine): countable, by tool 3.
  Every approach must feed in non-computable data, such as Leary's parameter `S`.
- **Simple ambient `H`:** no proper nontrivial quotients.
- **Free products of simple groups:** a normal subgroup meeting both factors trivially is free (Kurosh), hence
  not perfect.
- **Classical small cancellation over free groups:** by Lyndon's identity theorem the relation module of an
  aspherical `C'(1/6)` presentation is a direct sum of cyclic modules over the relators. It is not finitely
  generated when infinitely many independent relators are needed, so such quotients are not FP_2. Only a
  bounded remark: graphical versions (Brown–Leary) escape through acyclic relator complexes.
- **Type FP part:** any group with torsion is excluded, including every Thompson-like or topological full group.

## 5. Candidate constructions (open)

**(C1) Restriction to invariant sets.** `H = A(G)`, the alternating full group of an ample groupoid `G` over a
Cantor space with uncountably many minimal closed invariant sets `Y`. Needed:
- (a) `H` finitely presented;
- (b) restriction `H -> A(G|_Y)` onto;
- (c) the kernel perfect, for example because an element trivial on `Y` is the identity near `Y` when germs at
  `Y` are determined by their restriction to `Y`, so the kernel is a union of alternating groups of clopen
  reductions away from `Y`;
- (d) `A(G|_Y)` simple (Nekrashevych, minimal effective Hausdorff groupoids);
- (e) distinct `Y` separated by elements of `H`.

Then tool 2 gives uncountably many simple FP_2 quotients. Test case:
`G = G_V × (Z ⋉ {0,1}^Z)` on `C × {0,1}^Z`, with `Y = C × X_α` for Sturmian subshifts `X_α`, `α` irrational.
- Minimality and effectiveness of `G_V × (Z ⋉ X_α)` hold.
- Finite generation of `A(G)` looks plausible: controlled copies of `V` over clopens of the shift, conjugated by
  the shift and by `V`.
- Finite presentation (a) is the crux and unknown to this lane. The subgroup `C(C, Z) ⋊ V` of controlled shifts
  appears inside; whether it is finitely presented is a cloning-system question.

**(C2) Uniform relators over Leary's parameter.** Find a finitely presented `H = ⟨X | R_0⟩` and loops `Γ` whose
level-`n` images `P_n` are perfect subgroups, such that `H/⟨⟨P_n : n ∈ S⟩⟩` is simple for uncountably many `S`.
Maximality forces: killing any additional `P_m`, `m ∉ S`, collapses the quotient. No candidate yet.

**(C3) Type FP.** A torsion-free simple group acting on a CAT(0) complex with a Morse function whose level-set
links are acyclic but not simply connected, branched in Leary's way. Burger–Mozes lattices have graph links, so
they need higher-dimensional analogues. No candidate.

## 6. Sharpest next targets

1. Is `A(G_V × (Z ⋉ {0,1}^Z))` (or any expansive non-minimal Thompson-like group with uncountably many minimal
   invariant sets) finitely presented? A yes, together with (b), (c) and (e), answers part (i).
2. Independently: prove that the kernel in (C1)(c) is perfect for effective groupoids with infinite orbits, which
   reduces (C1) to finite presentability.
