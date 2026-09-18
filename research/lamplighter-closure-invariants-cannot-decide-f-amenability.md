---
rg: 2
id: lamplighter-closure-invariants-cannot-decide-f-amenability
kind: claim
title: No group invariant that holds for every lamplighter G wr Z and passes to coamenable overgroups and to quotients by amenable normal subgroups can decide whether Thompson's F is amenable; this covers uniform Ulam stability for every submultiplicative norm
distinct_from:
  thompson-f-relator-system-stable-in-permutations: that is pointwise stability of a finite relator system in permutations, which would decide soficity and hence amenability; this shows that the uniform (sup over all pairs) version of the same idea cannot decide anything, because it satisfies the lamplighter axiom.
  thompson-f-is-not-hyperlinear: that node notes in passing that uniform stability controls uniform, not pointwise, defect; this proves the barrier with comparison groups on both sides and names the three closure axioms every member satisfies.
  thompson-f-ore-obstructions-must-see-finite-support: that rules out leading-term and division-ring certificates of non-Ore pairs; this rules out stability, asymptotic-cohomology and separable bounded-cohomology certificates.
  thompson-f-is-amenable: that is the open problem; this is a barrier on which invariants could settle it in either direction.
artifacts:
  - research/artifacts/lamplighter-closure-verbatim-sources-2026-09-17.md
---

**OPEN.** The attempted proof is
`lamplighter-closure-invariants-cannot-decide-f-amenability-proof`, elementary on top of verbatim
imports from Fournier-Facio–Rangarajan (arXiv:2301.03970) and Monod (arXiv:2112.13741). It proves
items 1 to 4 and every individual kill in item 5, but not the completeness sentence of "What
survives", so the route is blocked on
`lamplighter-closure-covers-normalized-nonsubmult-targets`. See `## Attempts`. The
quotes are in the artifact. No priority is claimed.

All groups are countable. A subgroup `Λ ≤ Γ` is *coamenable* if `Γ/Λ` carries a `Γ`-invariant
mean. Consider three closure axioms for a class `P` of groups:

- **(L) lamplighters:** `G ≀ Z ∈ P` for every countable group `G`.
- **(Q) amenable quotients:** if `Γ ∈ P` and `N ⊴ Γ` is amenable, then `Γ/N ∈ P`.
- **(C) coamenable overgroups:** if `Λ ≤ Γ` is coamenable and `Λ ∈ P`, then `Γ ∈ P`.

Let `LC` be the smallest class satisfying (L), (Q) and (C), namely the intersection of all such
classes.

## Statement

1. **Every amenable group lies in `LC`.**
2. **`F_2 ≀ Z` lies in `LC` and is not amenable.**
3. **`F'` and `F` lie in `LC`.** The chain is `Γ_0 ≀ Z` (L), then `⟨Γ_0, g⟩` (Q, metabelian
   kernel), then `F'` (C), then `F` (C). Here `Γ_0 ≤ F'` is the subgroup of elements supported in
   a fixed compact interval and `g ∈ F'` pushes that interval off itself.
4. **Barrier.** Let `P` be any class satisfying (L), (Q) and (C). Then `LC ⊆ P`, so:
   - (no direction) no argument of the form "`F ∉ P`, hence `F` is not amenable" exists, because
     `F ∈ P`;
   - (yes direction) "`Γ ∈ P` implies `Γ` amenable" is false, because `F_2 ≀ Z ∈ P`.

   A certificate for either answer must therefore use a property that breaks at least one axiom.
   - For amenability, the certifying class `P ∋ F` must break at least one axiom, and if it
     keeps (Q) and (C) it must break (L): it must see the lamp group. Amenability itself
     satisfies (Q) and (C) and fails exactly (L).
   - For non-amenability, the complement of the certificate contains all amenable groups but not
     `F`, so it must break (L), (Q) or (C). If that complement satisfies (Q) and (C), then the
     witness must already hold for the single lamplighter `Γ_0 ≀ Z` of item 3.
5. **Members of the class that are killed.**
   - (a) *Uniform `U_f`-stability with a linear estimate*, for any family `U_f` of
     finite-dimensional unitary groups with bi-invariant submultiplicative norms (operator,
     Frobenius, Schatten-`p`, and `U(1)` with absolute value). It satisfies (L), (Q) and (C) by
     FFR `intro:thm:lamplighters`, `intro:prop:mapping` and `intro:prop:coamenable`. So every group in `LC` is uniformly
     `U_f`-stable.
     - The Kazhdan contrapositive dies at its first step. It would say: "exhibit a uniform
       asymptotic homomorphism `F → U_f` far from all homomorphisms, then use Kazhdan's theorem
       that amenable groups are uniformly stable". But no such asymptotic homomorphism exists.
       More precisely, every uniform asymptotic homomorphism `F → U_f` is uniformly close to one
       that factors through `F/F' = Z^2` (FFR, remark after `cor:F`). So the uniform
       finite-dimensional unitary data of `F` are those of an amenable group.
     - The `U(1)` special case kills every instability witness built from a non-trivial
       quasimorphism in the sense of Burger–Ozawa–Thom.
     - The converse "uniformly stable implies amenable" dies at `F_2 ≀ Z`. It also dies at `T` and
       `V`, which are uniformly stable (FFR `intro:thm:F`) and not amenable (`T`:
       `thompson-t-is-not-amenable`, and `T ≤ V`).
   - (b) *Vanishing of finitary asymptotic cohomology*, meaning `H^n_a(Γ, V) = 0` for all
     `n ≥ 1` and all finitary dual asymptotic Banach modules.
     - It holds for `F'` (FFR `cor:bsupp`, applied to `F'` in the proof of `cor:F`) and for `F_2 ≀ Z` (FFR
       `intro:thm:lamplighters:ac`).
     - So "vanishing implies amenable" dies at `F_2 ≀ Z`.
     - Non-vanishing cannot be witnessed on `F'`, and on `F` it could not produce instability,
       by (a).
   - (c) *Bounded acyclicity with separable dual coefficients*, meaning `H^n_b(Γ, E) = 0` for
     all `n > 0` and all separable dual Banach modules `E`.
     - It holds for `F` (Monod `thm:F:sep`), for every `G ≀ Z` (Monod `thm:sep`), and for every
       amenable group.
     - So neither direction can be certified. Johnson's cohomological characterization of
       amenability has to use non-separable coefficients such as `(ℓ^∞(Γ)/C)^*`, and that is
       exactly where the method must go.
     - Monod states the no-answer part himself: "this statement does not answer the amenability
       question".
   - (d) *Uniform non-approximability by `U_f`.* `F` is not uniformly `U_f`-approximable, but
     neither is the amenable group `S_3 ≀ Z` (FFR `cor:F:uniapprox`, with `Γ = S_3` non-abelian and
     `Λ = Z`). So "F is not uniformly approximable, hence not amenable" dies at `S_3 ≀ Z`.

## What survives

The obstruction names the step where every member dies: the **supremum over all pairs
`(g, h) ∈ Γ × Γ`** in the defect.
- For finite-dimensional submultiplicative targets, this supremum is what makes (L) true, through
  FFR's lamplighter vanishing.
- Two stability-type questions escape (L), and both are known to bear on the problem:
  - *Pointwise stability* of a finite relator system (in permutations, Hilbert–Schmidt or operator
    norm). FFR `cor:F:pwapprox`: if `F` is pointwise stable, it is not amenable. See
    `thompson-f-relator-system-stable-in-permutations`.
  - *Strong Ulam stability* (infinite-dimensional `U(H)`, operator norm). It fails for every
    countable group containing a free subgroup (FFR `rem:sharp:lamplighters`, from Burger–Ozawa–Thom), so it
    violates (L) at `F_2 ≀ Z`. Whether it coincides with amenability is open, as stated in FFR's
    introduction.

Conditional on `lamplighter-closure-covers-normalized-nonsubmult-targets`, the
stability-approximation family can only reach this problem through pointwise defects or
infinite-dimensional targets. Unconditionally, the list above is complete only among
**submultiplicative** targets.

## Attempts

- **Verbatim-import transplant from the stability-approximation family; refuted at the
  completeness sentence (2026-09-18, swarm-0917, e-f-transplant).** The route
  `lamplighter-closure-invariants-cannot-decide-f-amenability-proof` is kept as the attempt. A
  referee checked items 1 to 5 against the FFR TeX source and confirmed them: the three closure
  axioms are `intro:thm:lamplighters`, `intro:prop:mapping` and `intro:prop:coamenable` word for
  word; the chain `Γ_0 ≀ Z → ⟨Γ_0, g⟩ → F' → F` goes through `lem:metabelian:kernel`,
  `lem:coamenable:commuting` and `lem:coamenable:constructions`; and the kills in 5(a)–(d) match
  `cor:F`, `cor:bsupp`, `intro:thm:lamplighters:ac`, Monod `thm:F:sep`/`thm:sep` and
  `cor:F:uniapprox`.
  - *Where it dies.* The sentence naming the supremum over all pairs `(g, h)` as "the step where
    every member dies", and the conclusion that only pointwise defects and infinite-dimensional
    targets escape. Every import in item 5(a) assumes the norm is bi-invariant **and
    submultiplicative** — the Frobenius norm listed there is the unnormalized one. The normalized
    Hilbert--Schmidt norm and the normalized Hamming distance are finite-dimensional bi-invariant
    targets that are not submultiplicative (`‖E_11‖_2 = k^{-1/2} > ‖E_11‖_2^2`), and uniform
    stability for them uses the very same supremum over pairs. Nothing in the attempt shows that
    invariant satisfies (L), (Q) or (C), and FFR record that they do not know whether Thompson's
    groups are uniformly approximable in Hilbert--Schmidt norm. If amenable groups are uniformly
    stable for these targets — as in the flexible Hilbert--Schmidt result of De Chiffre--Ozawa--Thom,
    not verified here — that would be a Kazhdan-type contrapositive for non-amenability of `F`
    which this barrier does not block. So the survivor list is not shown to be complete.
  - *What it would take.* Either restrict the conclusion to submultiplicative targets, or settle
    `lamplighter-closure-covers-normalized-nonsubmult-targets`, which is now the one
    prerequisite of the route.
  - *Bookkeeping defects found in the same pass.* The artifact does not quote the statements of
    `cor:bsupp` or `intro:prop:coamenable:ac`, so "every quote is in the artifact" is overstated;
    the quote of the remark after `cor:F` inserts "asymptotically" where the source reads
    "uniformly close to the trivial one"; the Monod `thm:sep` quote swaps `\[...\]` for dollar
    signs; and 5(d), uniform non-approximability, is filed under class members although it fails
    (L) at `Z = {1} ≀ Z`. None of these changes any kill, since each rests on an explicit group.
