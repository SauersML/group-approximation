---
rg: 2
id: separable-subgroups-are-z-semilocal-root-closed
kind: claim
title: A homomorphism from Z_(S) into a residually finite group is determined by the image of 1, and every separable subgroup containing f(a) contains f(aZ_(S)); so tree actions with separable vertex stabilizers always put Z_(S) in a vertex group, and edges with infinitely many relative root primes help (SL) only through non-separable vertex groups
requires:
  - z-semilocalized-embeds-in-fp-rf-group
  - z-localized-fixes-a-vertex-or-end-of-every-tree
  - finite-root-prime-splittings-never-create-z-semilocal
  - bounded-root-primes-close-under-extensions-and-geometry
distinct_from:
  finite-root-prime-splittings-never-create-z-semilocal: that puts the smaller copy Z_(S ∪ P) in a vertex group when the edge inclusions have finitely many relative root primes P, while Z_(S) itself may climb a ray at primes of P; this does it when the vertex groups are separable, whatever the edge inclusions, and so settles route (b) outside non-separable splittings.
  bounded-root-primes-close-under-extensions-and-geometry: that is a census by root counting; this is a profinite mechanism, so it applies to separable subgroups of any group and to every residually finite quotient.
  z-semilocalized-embeds-in-fp-rf-group: that records that 1 in Z_(S) has S-order in every finite quotient; this turns that fact into uniqueness of Z_(S)-structures and root-closure of separable subgroups.
---

**ESTABLISHED** (lane proof; bh-invent-12, 2026-09-19; elementary; not independently reviewed). Items 1–2 are
folklore in spirit: they sharpen the standard facts that residually finite groups have no nontrivial divisible
elements and that `⟨a⟩` is not separable in `BS(1, p)`. No priority is claimed.

## Setting

`S` is any set of primes, `Z_(S)` the rationals with denominators prime to `S`, and an *S-number* is a positive
integer with all prime factors in `S`. A subgroup `K ≤ Λ` is *separable* if it is an intersection of finite-index
subgroups. For `a ∈ Z_(S)`, `aZ_(S) = cZ_(S)`, where `c` is the S-part of `a`.

## Theorem

1. **Uniqueness.** Let `Q` be residually finite and `f_1, f_2 : Z_(S) -> Q` homomorphisms with `f_1(1) = f_2(1)`.
   Then `f_1 = f_2`. So an element of a residually finite group carries at most one `Z_(S)`-structure.
2. **Root closure.** Let `f : Z_(S) -> Λ` be a homomorphism into any group, `K ≤ Λ` separable, and `f(a) ∈ K`.
   Then `f(aZ_(S)) ⊆ K`. Hence `f^(-1)(K)` is `0` or `cZ_(S)` for an S-number `c`. In particular, separable subgroups are closed under the `Z_(S)`-roots of their elements.
3. **Cyclic subgroups.** If `S` is not the set of all primes and `f` is injective, no `⟨f(a)⟩`, `a ≠ 0`, is
   separable. So a group in which every cyclic subgroup is separable contains no `Z_(S)` with `S` a proper subset of
   the primes; in particular it contains no `Z[1/p]`.
4. **Residually finite groups.** In residually finite `Λ`, every equalizer `{x : φ_1(x) = φ_2(x)}` of two
   homomorphisms into a residually finite group is separable. So item 2 applies to the following:
   - **(a) Centralizers.** If `u` commutes with `f(a)`, then `u` commutes with `f(aZ_(S))`.
   - **(b) Kernels.** Every homomorphism `ψ` from `Λ` to a residually finite group is injective on `f(Z_(S))`, or
     kills `f(cZ_(S))` for some `c`. In the second case `ψ f(Z_(S))` is finite cyclic of S-number order.
   - **(c) Retracts,** and, for finitely generated `Λ`, fixed subgroups of automorphisms.
5. **Trees.** Let `S` be a proper subset of the primes. Let `Λ` act on a simplicial tree whose vertex stabilizers are separable, and let `Z_(S) ≤ Λ`. Then
   some vertex stabilizer contains `cZ_(S) ≅ Z_(S)`. Nothing is assumed about edge groups, relative root primes or
   valence.
6. **Non-separable witnesses.** Let `S` be a proper subset of the primes. Let `Λ` act on a tree, and suppose `Z_(S) ≤ Λ` meets no vertex stabilizer in a
   copy of `Z_(S)`. Then `Z_(S)` fixes an end `ξ` and no vertex. For every vertex `w` on a ray to `ξ` far enough
   out, `Stab(w)` is not separable, and its closure (the intersection of the finite-index subgroups containing it)
   contains a copy `cZ_(S)`.

## Proof

**1.**
- Let `π : Q -> F` be a finite quotient. `π f_i` has finite image, so its kernel has finite index in `Z_(S)`.
- Finite-index subgroups of `Z_(S)` are `mZ_(S)` with `m` an S-number. A finite quotient of `Z_(S)` is
  `q`-divisible for every `q ∉ S`, so it has no `q`-torsion.
- `Z -> Z_(S)/mZ_(S)` is onto. So `π f_i` is determined by `π f_i(1) = π(g)`, and `π f_1 = π f_2` for every `π`.
- `Q` is residually finite, so `f_1 = f_2`.

**2.**
- Let `L ⊇ K` have finite index. Then `f^(-1)(L)` is a finite-index subgroup `dZ_(S)` containing `a`, so `d`
  divides the S-part of `a`, and `f^(-1)(L) ⊇ aZ_(S)`.
- Intersecting over all such `L` gives `f(aZ_(S)) ⊆ K`.
- So `B = f^(-1)(K)` contains `c_a Z_(S)` for each `a ∈ B`, where `c_a` is the S-part of `a`. It is a subgroup, and
  `c Z_(S) + c' Z_(S) = gcd(c, c') Z_(S)`. So `B = c Z_(S)`, where `c` is the gcd of the `c_a`, which is attained on
  finitely many `a`.

**3.** By item 2, `⟨f(a)⟩ ⊇ f(aZ_(S))`. But `aZ_(S) ≅ Z_(S)` is not cyclic unless `Z_(S) = Z`, i.e. `S` is the set
of all primes.

**4.**
- **Equalizers are closed.** Homomorphisms are continuous for the profinite topologies. A residually finite group
  is Hausdorff in its profinite topology, so the diagonal of `Q × Q` is closed. The equalizer is the preimage of
  the diagonal under `(φ_1, φ_2)`.
- **Closed means separable.** A closed subgroup `K` is separable: if `x ∉ K`, some coset `xN` (with `N` normal of
  finite index) misses `K`, so `x ∉ KN`, which has finite index.
- **The instances.**
  - A centralizer `C(u)` is the equalizer of `id` and conjugation by `u`.
  - A kernel is the equalizer of `ψ` and the trivial map.
  - A retract is the equalizer of `id` and the retraction.
  - `Fix(α)` is the equalizer of `id` and `α`.
- **The claims.**
  - (a) is item 2 for `K = C(u)`.
  - (b) is item 2 for `K = ker ψ`, together with injectivity of `f`.
  - (c) is item 2.

**5.**
- Elements of `Z_(S)` have roots of unboundedly large order, and translation lengths are multiplicative on
  hyperbolic elements. So every element of `Z_(S)` is elliptic.
- By `z-localized-fixes-a-vertex-or-end-of-every-tree`, `Z_(S)` fixes a vertex, and we are done, or it fixes an end
  `ξ`. In the second case, `Z_(S) = ⋃_j (Z_(S) ∩ Stab(w_j))` along a ray `(w_j)` to `ξ`.
- For large `j` the intersection contains some `a ≠ 0`. `Stab(w_j)` is separable, so by item 2 it contains
  `aZ_(S)`.

**6.**
- For `w` far out on the ray, `Stab(w)` contains some `f(a)`, `a ≠ 0`. If it were separable, it would contain
  `f(aZ_(S))` by item 2, against the hypothesis.
- The closure `K̄` of `K = Stab(w_j)` is separable and contains a nonzero element of `Z_(S)`, so `K̄ ⊇ cZ_(S)` by
  item 2.
- `Z_(S)` fixes no vertex: otherwise that stabilizer would contain `Z_(S)` itself. ∎

## Calibration

- **`BS(1, p) = Z[1/p] ⋊ Z`** is residually finite. Its Bass–Serre vertex group `⟨a⟩` meets `Z[1/p] = Z_(S)`
  (`S` = the primes other than `p`) in `Z`, which is not of the form `cZ[1/p]`. So `⟨a⟩` is not separable, as is
  well known, and `Z[1/p]` is an ascending union along a ray. This is the prototype of item 6.
- **The Euler lamplighter `G_l`** (`z-localized-embeds-in-fg-rf-soluble-group`) is residually finite and contains
  `Z_(l)` in `M`.
  - `M` is the kernel of `G_l -> Z ≀ Z`, so it is separable, and it is `Z_(l)`-root-closed as item 4(b) requires.
  - `⟨f_0⟩` is not separable (item 3).

## Route choice for (SL): route (a), with route (b) reduced to non-separable splittings

**Route (b), edges with infinitely many relative root primes.**
- By item 5, such edges are useless whenever the vertex groups are separable. This covers:
  - doubles and HNN extensions along the identity (vertex groups are retracts);
  - splittings in which the vertex groups are closed in the profinite topology, for instance the efficient graphs
    of groups of Wilton–Zalesskii (recalled), such as the JSJ splittings of 3-manifold groups;
- Route (b) survives only in the `BS(1, p)` form of item 6: a non-separable vertex group whose profinite closure
  already contains `Z_(S)`, so the profinite topology sees the divisible direction before the group does.
  - The natural shape is an ascending HNN extension of a finitely presented tame `B` by an injective endomorphism
    `φ`, where `φ(B)` has infinitely many relative root primes. `Z_(S)` then sits in `⋃_k t^(-k) B t^k`.
  - Free `B` is excluded (Borisov–Sapir mapping tori, `finite-root-prime-splittings-never-create-z-semilocal`).
  - So is virtually nilpotent `B`: an injective endomorphism has finite-index image there.
  - Mihailova fibre products have infinitely many relative root primes, but are not images of injective
    endomorphisms of `F_2 × F_2`, since they are not finitely presented.
  - No candidate `B` is known.

**Route (a), one irreducible piece.** Candidates and verdicts:

| candidate | contains `Z_(S)`? | reason |
|---|---|---|
| lattices in products of trees (Rattaggi, Kimberley–Robertson, Janzen–Wise), Euclidean building lattices | no | CAT(0): `bounded-root-primes-close-under-extensions-and-geometry` item 3 |
| Deligne-type central extensions `Z -> Γ̃ -> Γ` with `Γ` a residually finite lattice | no | item 4(b): `Z_(S)` meets `Z` in `0`, so it injects into `Γ`, which is CAT(0) or linear |
| any extension `N -> Λ -> Q` with `Q` residually finite and `N`, `Q` without `Z_(S)` | no | item 4(b) |
| LERF, or merely cyclic-subgroup separable, groups: free, surface, limit groups, polycyclic, virtually compact special, closed 3-manifold groups (Hamilton, recalled) | no | item 3 |
| automaton groups | no | `automaton-groups-see-only-smooth-periods` (bh-free-16) |
| **overgroups of the Euler lamplighter `G_l` inside `Aut(G_l)`** | **open, live** | see below |
| characteristic-0 KMS-type module extensions; `K_2`-repaired Steinberg groups | open | as recorded on `z-semilocalized-embeds-in-fp-rf-group` |

**The `Aut` reformulation (new candidate class).**
- **The equivalence.** (SL) holds iff some finitely generated residually finite `G ⊇ Z_(S)` with trivial centre has
  a finitely presented subgroup `P` with `Inn(G) ≤ P ≤ Aut(G)`.
  - (⇐) `Aut(G)` is residually finite (Baumslag), and `Inn(G) ≅ G`.
  - (⇒) Take `G = Λ * Z`, which has trivial centre, and `P = Inn(G)`.
- **The candidate `G_l`.** `G_l` has trivial centre. A central `(m, h)` has `h = 1`, since `H` acts faithfully on
  `M`, and then `m ∈ M^x = 0`.
- **Its automorphisms, as found so far.**
  - The scalars `Z_(l)^×` act on `M`.
  - The **Pochhammer automorphism** is `δ = diag(c_j)` on `M`, with `c_j = ∏_(i=1)^j (1 + l i)` and inverses for
    negative `j`. It normalizes `H`: `δ β δ^(-1) = β` and `δ x δ^(-1) = x β^(-1)`.
- **Why these do not finish.** `⟨x, δ⟩ ⊇ Z ≀ Z` is metabelian over `A = ⊕_k ⟨β_k⟩ ≅ Z[x^±]`, and `δ` acts
  trivially on `A`.
  - Its Bieri–Strebel complement contains the antipodal pair `±χ_x`, so it is not finitely presented.
  - A finitely presented `P` therefore needs automorphisms that move `A` in the `δ` direction, the analogue of
    Baumslag's letter `s` with `a^s = a a^t`.
  - **Baumslag's letter cannot act on `M`.** An automorphism of `M ⊗ Q` conjugating `β` to `β β_1` would match
    spectra. But `β β_1 = diag((1 + lj)(1 + l(j − 1)))`, and `(1 + lj)(1 + l(j − 1)) = 1` would need
    `2j − 1 + l j(j − 1) = 0`, which is impossible because the left side is odd. Meanwhile `β f_0 = f_0`.
  - So `P` must reach a finitely presented overgroup of `H` by some other mechanism, or use automorphisms of `G_l`
    that do not preserve `M`. This is the sharp open question of the route.

## Lesson for general BH

**The profinite topology cannot see a divisible direction. It can only swallow it whole.**
- In a residually finite group, a `Z_(S)` is determined by one element, and every separable subgroup containing a
  nonzero element of it contains a finite-index copy of it.
- **Consequences.**
  - Tree constructions with separable vertex groups never create divisibility, whatever their edge inclusions.
  - Residually finite quotients and centralizers either keep the whole `Z_(S)` or kill a finite-index copy of it.
  - LERF and cyclic-subgroup-separable groups are excluded wholesale.
- **Where divisibility must come from.** For `GL_n(Q)` via (SL), the only live mechanisms are ones whose
  finite-index subgroups already contain the divisible direction in their closure:
  - `BS(1, p)`-type non-separable ascents;
  - Euler-type module extensions, now reformulated as finitely presented subgroups of `Aut(G_l)`.
