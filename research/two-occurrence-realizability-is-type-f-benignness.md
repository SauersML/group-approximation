---
rg: 2
id: two-occurrence-realizability-is-type-f-benignness
kind: claim
title: Type F Mikhailova triples for a word problem are exactly type F benign relation subgroups; the Aanderaa--Cohen--Boone tower makes every halting subgroup type F benign
distinct_from:
  two-occurrence-pattern-reductions-are-power-closed: That reduces the two-occurrence window to the existence of a type F Mikhailova triple (H, S, phi) and leaves it open; this identifies such triples with type F benign relation subgroups, shows the literal single-group question is trivial, reduces the universal question to one finitely presented group, and proves the type F analogue of Higman's key benign lemma for halting subgroups.
  some-type-f-group-has-re-complete-word-problem: That is many-one completeness of WP(G_M); this concerns letter-local membership realizations of the word problems of OTHER groups in type F subgroups of type F groups.
  higman-rope-trick-group-is-never-fp3: That kills the rope trick, the step from a benign subgroup to an embedding, above FP_2; this is about the benign step itself, which in type F survives the torsion and finiteness obstructions that block embeddings.
---

**ESTABLISHED (proposed, 2026-09-18; referee welcome).** Let `G = F(A)/N` be
finitely generated, `A` finite, `F = F(A)` free. For `m ∈ {2, 3, ..., ∞}` or
`m = F` (finite `K(π,1)`) call a subgroup `N ≤ K` of a group `K` of type `F_m`
**`F_m`-benign** if there are a group `Λ ⊇ K` of type `F_m` and a subgroup
`Σ ≤ Λ` of type `F_m` with `Σ ∩ K = N`. (Higman's benign subgroups are the case
"`Λ` finitely presented, `Σ` finitely generated".)

1. **Triples are benign relation subgroups.** The following are equivalent.
   - (i) There are a group `H` and a subgroup `S ≤ H`, both of type `F_m`, and a
     free-monoid homomorphism `phi : (A ∪ A^-1)* -> H`, with
     `v =_G 1 <=> phi(v) ∈ S` (a type `F_m` Mikhailova triple).
   - (ii) The same, with `phi` a group homomorphism `F -> H` (so `phi(a^-1) = phi(a)^-1`).
   - (iii) `N` is `F_m`-benign in `F`.
   - (iv) `G ≅ D/(D ∩ S)` for a finitely generated `D ≤ H` and type `F_m` groups
     `S ≤ H` with `D ∩ S ⊴ D`.

   Each gives a linear-size inverse-respecting two-occurrence reduction
   `v -> [phi(v), q]` of `WP(G)` to the word problem of the type `F_m` group
   `K = H *_S (S × <q>)`.
2. **The literal question is trivial.** For `G = G_M`, which is of type `F`
   and has r.e.-complete word problem, `(G_M, 1, id)` is a type `F` triple. So the
   question left open by `two-occurrence-pattern-reductions-are-power-closed` has
   content only in its universal form: does every finitely generated recursively
   presented `G` have a type `F` (or `F_m`) triple?
3. **The universal form is one statement about one finitely presented group.**
   `F_m`-benign subgroups are closed under preimages along homomorphisms of
   finitely generated free groups, under finite intersections (diagonal trick),
   and under images along injective maps into type `F_m` groups. Hence every
   finitely generated recursively presented group has a type `F_m` triple iff
   the relation subgroup `N_U ⊴ F(B)` of Higman's universal finitely presented
   group `U = F(B)/N_U` is `F_m`-benign. Here `N_U` is the normal closure of
   finitely many words.
4. **Sandwich.** "`G` embeds in a group of type `F_m`" implies "`N` is
   `F_m`-benign", which implies "`WP(G)` two-occurrence-reduces into a type
   `F_m` group". The first implication is not reversible: every finite group
   has type `F` triples (take `S = N`, of finite index in `F`), and so does every
   subgroup of `Γ/M` with `Γ` and `M ⊴ Γ` of type `F`, torsion included. None of
   these groups with torsion embeds in a group of type `F`. In the other
   direction, an opposite-sign two-occurrence reduction into a type `F_m` group
   `K` gives only `N = f^{-1}(C_K(Q))` for a homomorphism `f : F -> K`. That is
   benignness with a centralizer, which need not be of type `F_m`, as the
   witness `Σ`.
5. **Type F Higman key lemma (halting subgroups).** Let `M` be any modular
   machine, with halting set `Hal ⊆ N^2`, base group
   `B = <t, x, y | xy = yx> ≅ Z * Z^2` and tower `G'_M`. Then the halting subgroup
   `T_M = <t(s) : s ∈ Hal>`, free on these generators, is `F`-benign in `B`, with
   witness `Λ = G'_M` (type `F`) and `Σ = <t, r_1, ..., r_n>` (free of rank `n+1`):

       <t, r_1, ..., r_n>  ∩  B  =  T_M.

   So every halting set of a modular machine, and hence every r.e. subset of
   `N` (through the universal modular machine of `some-type-f-group-has-re-complete-word-problem`),
   is represented by a type `F` benign subgroup of the type `F` group `Z * Z^2`.
   By item 3, `h^{-1}(T_M)` is `F`-benign in `F(A)` for every homomorphism
   `h : F(A) -> B`.

**What this leaves for Zaremsky 1.1.** At two occurrences with opposite signs,
a word-problem obstruction to type `F_{n+1}` hosts can only work if `N_U` is
not `F_{n+1}`-benign. The obstruction is dead at level `F_{n+1}` as soon as
`every-re-normal-subgroup-of-a-free-group-is-type-f-benign` holds. That
statement asks for the benign half of Higman's embedding theorem with type `F`
witnesses. Item 5 proves its base case. What is missing is Higman's passage
from halting subgroups to normal closures, which in the classical proof uses
joins `<A, B>` of benign subgroups. The classical join witness
`<S_A, S_B> ≤ L_A *_K L_B` is only known to be finitely generated. Its
splitting is governed by `A`, `B` and `A ∩ B`, which are infinitely generated,
and no argument makes it of type `F`. So the join (or directly the normal
closure) is the exact open step. The
embedding half (the rope trick) is dead above `FP_2` by Fournier-Facio--Zaremsky
Theorem B, and it is not needed here. The two-occurrence window can therefore
close even if Problem 1.1 has a negative answer.

Proof: route `two-occurrence-realizability-is-type-f-benignness-proof`.
