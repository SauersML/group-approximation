---
rg: 2
id: thompson-t-mixed-identity-problem-is-decidable
kind: claim
title: For every k the k-variable mixed identities of Thompson's groups F and T form a recursive set
distinct_from:
  a2-kernel-removal-forces-recursive-kernel: that shows one-variable mixed identities of a finitely presented simple group are co-r.e., and that a non-recursive set would give a non-removable type [A_2] kernel; this proves the set recursive for T and F in every number of variables.
  homeo-circle-three-arc-commutator-word-is-mixed-identity: that exhibits one nontrivial mixed identity of T and F; this decides, for an arbitrary word, whether it is a mixed identity.
  fp-simple-group-with-nonrecursive-mixed-identities: that asks for some infinite finitely presented simple group with a non-recursive set of mixed identities; this shows T is not such a group.
artifacts:
  - research/artifacts/solve-mixed-identity-undecidable-2026-09-13.md
---

**ESTABLISHED** by `thompson-t-mixed-identity-decision-procedure-proof`.

**Setting.**
- `T` is the group of piecewise-linear homeomorphisms of `S^1 = R/Z` with
  finitely many breakpoints, all dyadic, slopes integer powers of 2, mapping
  `D = Z[1/2]/Z` onto itself.
- `F` is the analogous group of homeomorphisms of `[0,1]`.
- Fix finite generating sets. For `G in {F, T}` and `k >= 1`, `J_k(G) ⊆ G * F_k`
  is the set of `w` with `w(g_1, ..., g_k) = 1` for all `(g_1, ..., g_k) in G^k`.

**Theorem.** For `G in {F, T}` and every `k >= 1` there is an algorithm that,
given a word in the generators of `G` and in `x_1^(±1), ..., x_k^(±1)`, decides
whether it lies in `J_k(G)`.

**Method.**
- The complement is semi-decided by searching substitutions. The new content
  is membership.
- `w` fails to be a mixed identity exactly when some dyadic point has a
  non-closing trajectory. In that trajectory each `x_m` is realized only through
  a finite partial injection of dyadic points that preserves the order (for `F`)
  or the cyclic order (for `T`), and every such partial injection extends to an
  element of `G`.
- Existence of a trajectory of one combinatorial type asks for `Z[1/2]`-points
  of a rational polyhedron cut out by equations and strict inequalities. Smith
  normal form over `Z` and linear programming over `Q` decide it.

**Consequences.**
- `thompson-t-relative-automorphism-actor-kernel-is-recursive`: for `n >= 2`,
  the kernel of the action of `Aut_T(T * F_n)` on `Hom_T(T * F_n, T)` is
  recursive. So `T` gives no counterexample to the first part of FFWZ
  Question 5.9 through Attempt 2 of `a2-pairs-embed-in-a2-pairs-with-fng-kernels`.
- The computability obstruction to BFFHZ Question 3.2 for `G = T` disappears.
  Were the quotient finitely presented, the kernel would be r.e. It is co-r.e.
  anyway, so nothing is forced. Question 3.2 itself is not answered.

**Not claimed.**
- No complexity bound. The type enumeration is exponential in the word length.
- No other group. The procedure needs piecewise-linear data over a ring where
  these feasibility questions are decidable, plus an extension lemma for finite
  partial maps. Both are checked here only for `F` and `T`, not for the
  Higman--Thompson groups `T_(n,r)`, Stein groups or irrational-slope groups.

**Credit.** Not found stated in BFFHZ, who say it is "unclear what to expect,
even for example for Thompson's group T" about Question 3.2 (extracted text on
MSI, l.694–698). No literature search beyond that source.
