---
rg: 2
id: kourovka-15-19a-some-grigorchuk-groups-are-not-finite-state
kind: claim
title: Kourovka 15.19(a), "some" form, for p = 2. There is a computable, non-periodic ω, with every symbol occurring infinitely often, such that Grigorchuk's 2-group G_ω has word problem outside exponential time. So G_ω is not isomorphic to any finitely generated group acting faithfully by finite automata on a regular rooted tree, and in particular is not in F_2
distinct_from:
  finite-recursion-gives-no-computable-depth-bound: that shows finite recursion alone forces no computable depth bound, using Bartholdi–Mitrofanov's group with non-recursive word problem; this uses the exponential-time bound that finite automata DO force, and places a computable Grigorchuk group outside it.
  fp-self-similar-groups-with-arbitrarily-hard-word-problem: that asks for finitely presented self-similar groups with arbitrarily hard (decidable) word problems; the groups G_ω here are infinitely presented and not finite-state, so they say nothing about that target.
---

**OPEN (proof claimed, under review; lane bh-k1519, 2026-09-19).** The argument below is a lane
proof and has not been independently reviewed. Two inputs are recalled, not read at source: the
branch property of G_ω (step 3), and the identification of the 1986 paper's p = 2 family with the
binary G_ω (scope). No priority is claimed. The argument is elementary, and the problem's own
preamble uses the same complexity principle, so it may well be known to experts. Kourovka
arXiv:1401.0300v46 still lists 15.19(a) as open.

## Statement

Kourovka 15.19, verbatim, from the notebook's LaTeX source (v46), proposed by L. Bartholdi and
S. Sidki:

> Let p be a prime, and F_p the class of finitely generated groups acting faithfully on a
> p-regular rooted tree by finite automata. Any group in F_p is residually-p (residually in the
> class of finite p-groups) and has word problem that is solvable in (at worst) exponential time.
> There exist therefore groups that are residually-p, have a solvable word problem, and do not
> belong to F_p; though no concrete example is known. For instance:
> a) Is it true that some (or even all) the groups given in (R. I. Grigorchuk, Math. USSR–Sb., 54
> (1986), 185–205) do not belong to F_p when the sequence ω is computable, but not periodic?

Part (b) is answered in the notebook (Dantas–Oliveira–Santos 2024). Part (a) has no comment.

**Claim.** Take Grigorchuk's binary family G_ω = ⟨a, b_ω, c_ω, d_ω⟩, ω ∈ {0,1,2}^ℕ. There is a
computable ω, not eventually periodic and containing each of 0, 1, 2 in every window of length 8,
such that WP(G_ω) ∉ E = ⋃_c DTIME(2^{cn}). Since every finitely generated subgroup of a group of
finite-state automorphisms of a regular rooted tree has word problem in E, G_ω belongs to no
class F_d, and in particular G_ω ∉ F_2.

G_ω is then a concrete, residually-2 group with solvable word problem that is not in F_2. This
answers the "some" form of 15.19(a) for p = 2, provided the scope caveat below holds. The "all"
form stays open, e.g. for ω computable in polynomial time.

**Scope caveat.** 15.19(a) cites the p-groups paper (Math. USSR–Sb. 54 (1986)). This claim is
proved for the binary family of Grigorchuk 1984. That this is the p = 2 case of the cited family
is recalled, not checked. Odd p is not covered: step 4 uses that two involutions generate a
metabelian group, and ⟨a, z⟩ with a, z of order p need not be metabelian.

## Attempts

### Attempt 1 (bh-k1519): proof via exponential-stretch detectors plus time hierarchy

**Conventions (Grigorchuk 1984).**
- ω₁ selects the first coordinates of b, c, d:
  - 0 ↦ (a, a, 1);
  - 1 ↦ (a, 1, a);
  - 2 ↦ (1, a, a).
- Then b_ω = (u_b, b_{sω}), c_ω = (u_c, c_{sω}), d_ω = (u_d, d_{sω}), with u_ℓ ∈ {a, 1}. Here s is
  the shift and a swaps the two subtrees.
- ω₁ is therefore determined by the unique letter ℓ ∈ {b, c, d} with u_ℓ = 1. Write ℓ, ℓ′ for the
  same letter read in G_η and in G_{sη}.
- Let F be the free group on a, b, c, d.

**Step 1 (level-1 test).** Let η be arbitrary and ℓ ∈ {b,c,d}. Put C_ℓ = [ℓ, aℓa] ∈ F.
- In G_η, ℓ = (u_ℓ, ℓ′) and aℓa = (ℓ′, u_ℓ).
- If u_ℓ = 1, these are (1, ℓ′) and (ℓ′, 1), which commute, so C_ℓ = 1.
- If u_ℓ = a, then C_ℓ = ([a,ℓ′], [ℓ′,a]), and [a,ℓ′] ≠ 1. Indeed aℓ′aℓ′ = (ℓ″u′, u′ℓ″) with
  ℓ″ ≠ 1 and u′ ∈ {1, a}. Also aℓ″ ≠ 1, since a ∉ Stab(1) ∋ ℓ″.

**Step 2 (moving the test into F″).** Put D_{ℓ,g} = [C_ℓ, g⁻¹C_ℓ g] ∈ F″ for a word g.
- If u_ℓ = 1, then D_{ℓ,g} = 1.
- If u_ℓ = a, some g gives D_{ℓ,g} ≠ 1, by step 3.

**Step 3 (branch input, recalled).** For η with every symbol occurring infinitely often:
- G_η is an infinite 2-group (Grigorchuk 1984) and a branch group (Grigorchuk, "Just infinite
  branch groups", 2000; Bartholdi–Grigorchuk–Šunić, "Branch groups").
- In a branch group, the normal closure of any g ≠ 1 contains Rist(n)′ for some n (recalled).
- Rist(n) has finite index. So Rist(n)′ abelian would make G_η virtually solvable, impossible for
  an infinite finitely generated torsion group.
- Hence the normal closure of C_ℓ ≠ 1 is non-abelian. So some two conjugates C_ℓ^x, C_ℓ^y fail to
  commute, and g = y x⁻¹ works.

**Step 3′ (uniform finite list).**
- Let Ω₈ be the closed set of sequences in which each of 0,1,2 occurs in every window of length 8.
- Whether a fixed word acts nontrivially on G_η depends only on finitely many η_i: the action on
  level m depends only on η₁…η_{m−1}. So "D_{ℓ,g} ≠ 1" is an open condition on η.
- The compact set {η ∈ Ω₈ : u_ℓ(η₁) = a} is covered by these open sets, so finitely many g
  suffice: a finite list Γ_ℓ.
- Thus, for η ∈ Ω₈: u_ℓ(η₁) = 1 ⟺ D_{ℓ,g} = 1 in G_η for every g ∈ Γ_ℓ.
- The lists are fixed constants; their existence is all the argument needs.

**Step 4 (lifting through one level).** Given η₁, let z ∈ {b,c,d} be a letter with u_z(η₁) = a.
Define the endomorphism L_η of F by a ↦ aza, and ℓ ↦ ℓ for ℓ = b, c, d.
- For every word w, L_η(w) fixes level 1. Its right section is w, read in G_{sη}. Its left section
  is τ_η(w), where τ_η : a ↦ z, ℓ ↦ u_ℓ(η₁) is a letter substitution.
- τ_η(w) lies in ⟨a, z⟩ ≤ G_{sη}. That subgroup is generated by two involutions, so it is dihedral,
  hence metabelian.
- For w ∈ F″ we get τ_η(w) = 1, so L_η(w) = (1, w). Hence L_η(w) = 1 in G_η ⟺ w = 1 in G_{sη}.
- Also L_η(F″) ⊆ F″ and |L_η(w)| ≤ 3|w|.

**Step 5 (detectors for ω_k).** For k ≥ 2, ℓ ∈ {b,c,d} and g ∈ Γ_ℓ, put
W_{k,ℓ,g} = L_ω L_{sω} ⋯ L_{s^{k−2}ω}(D_{ℓ,g}).
- Building it uses only ω₁…ω_{k−1}, and |W_{k,ℓ,g}| ≤ K·3^k with K independent of k.
- By step 4, W_{k,ℓ,g} = 1 in G_ω ⟺ D_{ℓ,g} = 1 in G_{s^{k−1}ω}.
- By step 3′, ω_k is the code of the unique ℓ with W_{k,ℓ,g} = 1 for all g ∈ Γ_ℓ (when
  s^{k−1}ω ∈ Ω₈).

**Step 6 (complexity transfer).** Suppose WP(G_ω) ∈ DTIME(2^{cn}) for generators a, b, c, d; E is
robust under a change of finite generating set.
- Compute ω₁, ω₂, … in turn with step 5.
- This computes ω_k in time Σ_{j≤k} poly(3^j)·2^{cK3^j} ≤ 2^{c′3^k}.

**Step 7 (the hard computable ω).** Fix the blocks ω_{4m+1} = 0, ω_{4m+2} = 1, ω_{4m+3} = 2 and
ω_{4m+4} = x_m ∈ {0,1,2}. Then ω ∈ Ω₈, and so is every shift of ω. Set t(k) = 2^{2^{2^k}}.
- Enumerate machines M_i, and give each i infinitely many stages. At the stage using block m, run
  M_i on input 4m+4 for t(4m+4) steps.
- If M_i halts with an output v ∈ {0,1,2}, set x_m = v + 1 mod 3; otherwise x_m = 0.
- Then ω is computable. No machine computes every ω_k within time t(k) for all large k: at
  infinitely many of its stages it would halt in time and output the value that x_m avoids.
- ω is not eventually periodic, since otherwise ω_k would be computable in linear time.
- Step 6's algorithm would run in time 2^{c′3^k} < t(k) for large k, contradicting this. So
  WP(G_ω) ∉ E.

**Step 8 (finite-state groups have word problem in E).** Let G be generated by finite-state
automorphisms of a d-regular rooted tree, and let s be the maximal number of states.
- A word of length n is a product automaton with at most s^n states.
- Triviality means every reachable state acts trivially on the first letter. That is a reachability
  check in time poly(s^n) = 2^{O(n)}.
- The same bound holds for finitely generated subgroups, and under change of generators. The
  15.19 preamble states this for p-regular trees.
- So G_ω, with WP(G_ω) ∉ E, is isomorphic to no group in any F_d.

**Items for the referee.**
- The step 3 branch inputs.
- The step 3′ openness and compactness argument.
- Step 4's left-section computation. The sign and coordinate conventions should be checked against
  Grigorchuk 1984.
- The scope caveat about p = 2 and the 1986 paper.

## Priority (unresolved)

Referee bh-ref-e passed the mathematics (b2679f2613). Priority is still open, so the node stays
OPEN.

The likely prior source is M. Garzon and Y. Zalcstein, "The complexity of Grigorchuk groups with
application to cryptography", Theoret. Comput. Sci. 88 (1991) 83–98, doi:10.1016/0304-3975(91)90074-C.
- **Abstract** (verbatim, from the University of Memphis Digital Commons record): "The Turing
  complexity of the word problems of a class of groups introduced by Grigorchuk (1985) is
  examined. In particular, it is shown that such problems of permutation groups of the infinite
  complete binary tree yield natural complete sets that separate time and space complexity classes
  if they are distinct."
- **What that suggests:** they show that WP(G_ω) has the complexity of ω. If so, the hard
  computable ω of steps 5–7 is already theirs.
- **Consequence:** 15.19(a) in "some" form would then follow at once from their theorem together
  with the exponential bound for finite-state groups stated in the problem itself. This node would
  then grade as attribution to Garzon–Zalcstein, with only the explicit combination as the lane's
  part.
- **Not read at source.** Elsevier's pages sit behind a bot wall from MSI. The open-archive PDF,
  the Elsevier API full-text view without a key, CORE and Unpaywall all returned no text on
  2026-09-19. Reading their §§2–4 needs the PDF supplied by hand.

## Sources

- Kourovka Notebook, arXiv:1401.0300v46, problem 15.19, read at source (LaTeX).
- R. I. Grigorchuk, Degrees of growth of finitely generated groups and the theory of invariant
  means, Izv. Akad. Nauk SSSR 48 (1984). Recalled: definitions, periodicity, and "WP(G_ω) is
  solvable iff ω is recursive", as quoted in secondary sources.
- R. I. Grigorchuk, Just infinite branch groups (2000); L. Bartholdi, R. I. Grigorchuk,
  Z. Šunić, Branch groups (arXiv:math/0510294). Both recalled for step 3.
- A. C. Dantas, J. R. Oliveira, T. M. G. Santos, arXiv:2405.16678, for 15.19(b), cited in the
  notebook.
