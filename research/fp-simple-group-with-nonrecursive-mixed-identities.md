---
rg: 2
id: fp-simple-group-with-nonrecursive-mixed-identities
kind: claim
title: Some infinite finitely presented simple group has a non-recursive set of k-variable mixed identities for some k
distinct_from:
  thompson-t-mixed-identity-problem-is-decidable: that proves the mixed identities of Thompson's group T recursive in every number of variables; this asks for some finitely presented simple group where they are not.
  a2-kernel-removal-forces-recursive-kernel: that proves the consequence of a non-recursive set of one-variable mixed identities for the Theorem C actor; this asks whether such a group exists at all.
  fp-simple-groups-embed-in-fp-simple-mif-groups: that asks whether mixed identities can be removed by passing to a finitely presented simple overgroup; this asks whether the set of mixed identities can be undecidable.
artifacts:
  - research/artifacts/solve-mixed-identity-undecidable-2026-09-13.md
---

**OPEN.** For a group `Γ` and `k >= 1`, let `J_k(Γ) ⊆ Γ * F_k` be the words `w`
with `w(g_1, ..., g_k) = 1` for all `(g_1, ..., g_k) in Γ^k`. The claim: some
infinite finitely presented simple `Γ` and some `k` have `J_k(Γ)` not recursive.

**Upper bound.** `Γ` has solvable word problem
(`simple-envelope-forces-solvable-word-problem`), so `J_k(Γ)` is co-r.e.: a
non-identity is witnessed by one substitution. The question is whether a
universal statement over `Γ^k` can hide a non-recursive `Π_1` set.

**Why it matters.** The route
`non-removable-a2-kernel-from-nonrecursive-mixed-identities` turns a witness into
a type `[A_2]` pair with non-removable kernel. That answers the first part of
FFWZ Question 5.9 negatively (`a2-pair-with-non-removable-kernel-exists`). The
same kernel makes `A/K` not recursively presented (as in
`a2-kernel-removal-forces-recursive-kernel` (c)), which answers BFFHZ Question
3.2 negatively for that `Γ`.

## Attempts

1. **MIF groups.** *Dies.* `J_k(Γ)` contains only the trivial word. This covers:
   - Thompson's `V` and every twisted Brin--Thompson group, highly transitive by
     BFFHZ (extracted text on MSI, l.154–156), hence MIF;
   - the Kac--Moody lattices (`fp-simple-kac-moody-lattices-are-mif`).
2. **Thompson's `T`.** *Dies.* `T` is not MIF
   (`homeo-circle-three-arc-commutator-word-is-mixed-identity`), but
   `thompson-t-mixed-identity-problem-is-decidable` decides `J_k(T)` for every
   `k`.
   - The procedure needs two things: piecewise-linear data over a ring with
     decidable feasibility, and an extension lemma for finite partial maps
     respecting the order.
   - Groups acting on an interval or the circle with such data and such flexibility
     are expected to fall the same way. Only `F` and `T` are checked.
3. **Hard dynamics of constants: where hardness cannot come from (heuristic).**
   A word `w` is evaluated along trajectories of length `|w|`, so each constant
   acts a bounded number of times. Long-orbit phenomena therefore do not enter
   directly, such as the Turing-machine elements behind undecidable torsion
   problems in Brin--Thompson groups. Any hardness has to sit in the existential
   quantifier: in which finite partial behaviours elements of `Γ` can realize. A
   candidate would be a non-MIF finitely presented simple group whose realizable
   finite partial behaviours are not decidable. Examples might be circle or line
   groups with rigid or non-piecewise-linear dynamics. None is known here, and
   the heuristic is not a theorem.
4. **Leavitt unit groups.** *Untested.* Their MIF status is undecided (Attempt 4
   of `fp-simple-groups-embed-in-fp-simple-mif-groups`). If they are not MIF,
   their mixed identities are unit-valued generalized polynomial identities of
   the Leavitt algebra. Decidability of those was not examined.
5. **A Kuznetsov-type certificate.** *No proof.* For simple `Γ`, a nontrivial
   value `w(g)` normally generates `Γ`. That only re-derives co-r.e. Membership
   in `J_k(Γ)` needs a certificate for a universal statement, and no general
   one was found.
