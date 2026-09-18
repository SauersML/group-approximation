---
rg: 2
id: lamplighter-closure-invariants-cannot-decide-f-amenability-proof
kind: route
title: Put amenable groups, F_2 wr Z and Thompson's F into the closure of lamplighters under amenable quotients and coamenable overgroups, then read off each uniform invariant from the Fournier-Facio–Rangarajan and Monod heredity theorems
target: lamplighter-closure-invariants-cannot-decide-f-amenability
requires:
  - thompson-t-is-not-amenable
  - lamplighter-closure-covers-normalized-nonsubmult-targets
artifacts:
  - research/artifacts/lamplighter-closure-verbatim-sources-2026-09-17.md
---

The sources are [FFR], arXiv:2301.03970, and [M], arXiv:2112.13741. Every import is quoted
verbatim in `research/artifacts/lamplighter-closure-verbatim-sources-2026-09-17.md` and cited by
its TeX label. `LC` is the intersection of all classes of countable groups that satisfy (L), (Q)
and (C). The class of all countable groups is one of them, and an intersection of such classes
again satisfies all three axioms. So `LC` is well defined and is itself closed under (L), (Q) and
(C).

**Item 1 (amenable groups).**
- `{1} ≀ Z = (⊕_Z {1}) ⋊ Z = Z`, so `Z ∈ LC` by (L).
- `Z` is an amenable normal subgroup of itself, so `{1} = Z/Z ∈ LC` by (Q).
- If `Γ` is amenable, `Γ/{1} = Γ` carries a `Γ`-invariant mean. So `{1}` is coamenable in `Γ`,
  and `Γ ∈ LC` by (C).

**Item 2.** `F_2 ≀ Z ∈ LC` by (L). It contains `F_2`, and subgroups of amenable groups are
amenable, so `F_2 ≀ Z` is not amenable.

**Item 3 (`F'` and `F`).** [FFR, proof of `cor:F`]: `F'` is the group of boundedly supported
elements, and after identifying `(0,1)` with `R` it is proximal and boundedly supported. Apply
[FFR, proof of `cor:bsupp`] with `Γ = F'`:
- `Γ_0` is the subgroup of elements supported in the image `J` of `[0,1]`;
- `g ∈ F'` satisfies `g(0) > 1`, so the intervals `g^i J` are pairwise disjoint and the conjugates
  `g^i Γ_0 g^-i` pairwise commute;
- every finite subset of `F'` lies in some conjugate `h Γ_0 h^-1`.

The four steps are then:
- (i) `Γ_0 ≀ Z ∈ LC` by (L).
- (ii) [FFR `lem:metabelian:kernel`] gives an epimorphism `Γ_0 ≀ Z → ⟨Γ_0, g⟩` with metabelian,
  hence amenable, kernel. So `⟨Γ_0, g⟩ ∈ LC` by (Q).
- (iii) [FFR `lem:coamenable:commuting`] (from [M, Proposition 10]) shows that `Γ_0` is coamenable
  in `F'`. Then [FFR `lem:coamenable:constructions`, item 1] with `K = Γ_0` and
  `H = ⟨Γ_0, g⟩` shows that `⟨Γ_0, g⟩` is coamenable in `F'`. So `F' ∈ LC` by (C).
- (iv) `F/F'` is abelian, hence amenable, so `F'` is coamenable in `F` [FFR, proof of `cor:F`].
  So `F ∈ LC` by (C).

**Item 4 (barrier).**
- If `P` satisfies (L), (Q) and (C), then `LC ⊆ P` by minimality. So `F ∈ P` by item 3 and
  `F_2 ≀ Z ∈ P` by item 2. Both bullets of item 4 follow.
- *Amenability certificates.* Suppose `P ∋ F` and `P` contains only amenable groups. Then `P` does
  not contain `F_2 ≀ Z`, so it breaks some axiom. If it keeps (Q) and (C), it cannot contain all of
  (L).
- *Non-amenability certificates.* Suppose the witness class `N ∋ F` contains no amenable group.
  Its complement `A` contains every amenable group and misses `F`, so `A` cannot satisfy all three
  axioms. If `A` satisfies (Q) and (C), then running steps (ii) to (iv) inside `A` shows that
  `Γ_0 ≀ Z ∈ A` would force `F ∈ A`. So `Γ_0 ≀ Z ∈ N`.
- *Amenability is a closure-class member only partially.* It satisfies (Q), since quotients of
  amenable groups are amenable. It satisfies (C) by [FFR `lem:coamenable:constructions`, item 2]
  with `K = {1}` and `H = Λ`: `{1}` is coamenable in the amenable group `Λ`, and `Λ` is coamenable
  in `Γ`, so `{1}` is coamenable in `Γ`, which means `Γ` is amenable. It fails (L) at `F_2 ≀ Z`.

**Item 5(a).** Fix a family `U_f` as in [FFR]. Let `P_U` be the class of uniformly `U_f`-stable
groups with a linear estimate.
- (L) holds by [FFR `intro:thm:lamplighters`] with `Λ = Z`.
- (Q) holds by [FFR `intro:prop:mapping`].
- (C) holds by [FFR `intro:prop:coamenable`].

So `LC ⊆ P_U`.
- *No direction.* The Kazhdan contrapositive would need `F ∉ P_U`, or at least `F` not uniformly
  `U_f`-stable. Both fail by item 3, and independently by [FFR `intro:thm:F`]. The refined form,
  that asymptotic homomorphisms of `F` are close to ones through `Z^2`, is [FFR, remark after
  `cor:F`].
- *Quasimorphisms.* `U(1)` with the absolute value is a bi-invariant submultiplicative norm on a
  finite-dimensional unitary group, so `F` is uniformly `U(1)`-stable. By Burger–Ozawa–Thom, as
  quoted in [FFR] ("instability of groups admitting non-trivial quasimorphisms"), any quasimorphism
  witness for instability dies at this step.
- *Yes direction.* `F_2 ≀ Z ∈ P_U` and is not amenable.
- *T and V.* By [FFR `intro:thm:F`], `T` and `V` lie in `P_U`. `T` is not amenable by
  `thompson-t-is-not-amenable`, and `V ⊇ T` is not amenable because subgroups of amenable groups
  are amenable.

**Item 5(b).**
- [FFR `cor:bsupp`], applied to `F'` exactly as in the proof of `cor:F`, gives `H^n_a(F', V) = 0`
  for all `n ≥ 1` and all finitary modules.
- [FFR `intro:thm:lamplighters:ac`] with `Γ = F_2` and `Λ = Z` gives the same for `F_2 ≀ Z`, which
  is not amenable by item 2.
- The remaining sentence of 5(b) is (a) again.

**Item 5(c).**
- [M `thm:F:sep`] gives vanishing for `F`.
- [M `thm:sep`] gives vanishing for every `G ≀ Z`, in particular for `F_2 ≀ Z`.
- The amenable case is the classical vanishing, acknowledged verbatim in [M] ("except of course
  amenable groups").

So a separable-coefficient certificate can prove neither answer.
- Johnson's theorem characterizes amenability by vanishing for *all* dual modules. It is
  classical, and cited here only to say where a method would have to go; nothing in the claim
  depends on it.
- Monod's own caution is quoted in the artifact.

**Item 5(d).** [FFR `cor:F:uniapprox`] shows that `F` is not uniformly `U_f`-approximable, and
neither is `Γ ≀ Λ` for `Λ` infinite amenable and `Γ` non-abelian. Take `Γ = S_3` and `Λ = Z`. Then
`⊕_Z S_3` is locally finite, hence amenable, and its extension `S_3 ≀ Z` by `Z` is amenable.

**What survives.**
- [FFR `cor:F:pwapprox`] is quoted verbatim in the artifact.
- The failure of strong Ulam stability for countable groups containing free subgroups is quoted
  from [FFR `rem:sharp:lamplighters`]. It shows that strong Ulam stability violates (L) at
  `F_2 ≀ Z`.

**Scope.** Items 1 to 4 are proved in full here. Item 5 is by verbatim import. The TeX sources
were read directly for every quoted statement. The FFR proofs themselves (asymptotic cohomology)
were not re-verified.

**The gap (2026-09-18 referee).** The "What survives" conclusion — that the
stability-approximation family can reach the amenability of `F` only through pointwise defects or
infinite-dimensional targets — does not follow from items 1 to 5. Every import above carries FFR's
standing hypothesis that the norm is bi-invariant **and submultiplicative**, and the Frobenius norm
in the 5(a) list is the unnormalized one. The normalized Hilbert--Schmidt norm and the normalized
Hamming distance are bi-invariant finite-dimensional targets that are *not* submultiplicative
(`‖E_11‖_2 = k^{-1/2} > ‖E_11‖_2^2`), and uniform stability for them is defined by the same
supremum over all pairs `(g, h)`. Nothing here shows that this invariant satisfies (L), (Q) or (C),
so the survivor list is not shown to be complete. That is the content of
`lamplighter-closure-covers-normalized-nonsubmult-targets`, now required above: with it,
items 1 to 5 give the barrier as stated; without it, the barrier holds only for submultiplicative
targets. Items 1 to 4 and the individual kills in item 5 are unaffected — each rests on the
explicit groups `F'`, `F`, `F_2 ≀ Z`, `S_3 ≀ Z`, `T` and `V`, not on the completeness sentence.
