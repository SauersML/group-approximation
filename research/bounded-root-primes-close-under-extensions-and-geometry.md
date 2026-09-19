---
rg: 2
id: bounded-root-primes-close-under-extensions-and-geometry
kind: claim
title: Groups whose elements have roots at finitely many primes and whose torsion has finitely many prime orders form a class closed under subgroups, extensions and finite-root-prime splittings, containing all CAT(0), hyperbolic and finitely generated linear groups; so lattices in products of trees, Deligne-type central extensions and every extension built from them are not (SL) witnesses
distinct_from:
  finite-root-prime-splittings-never-create-z-semilocal: that closes the class under splittings; this adds extensions, geometric actions and an exact root formula, and runs the census of irreducible candidates for (SL).
  automaton-groups-see-only-smooth-periods: that excludes finite-state (translation-type) hosts on a rooted tree; this excludes geometric, linear and extension-built hosts, with no tree action.
---

**ESTABLISHED** (lane proof; bh-invent-12, 2026-09-18; elementary; not independently reviewed) for items 1–4.
The census entries marked *sketch* are not proved here. No priority is claimed; the lemmas may be folklore.

## Definitions

- `R_G(g) = {n >= 1 : g = h^n for some h ∈ G}`.
- `τ(G)` is the set of primes `p` such that `G` has an element of order `p`.
- `𝒩_τ` is the class of groups `G` with two properties:
  - `τ(G)` is finite;
  - for every `g ≠ 1`, only finitely many primes divide elements of `R_G(g)`.
- A group containing `Z_(S)` for a finite `S` is not in `𝒩_τ`, since `1 ∈ Z_(S)` has roots at every prime outside `S`.

## Theorem

1. **Root formula for trees.** Let `Λ` act on a tree without inversions.
   - If `g` fixes a vertex, then `R_Λ(g)` is the union of `R_(Stab w)(g)` over the vertices `w` fixed by `g`.
   - If `g` is hyperbolic, then `R_Λ(g) ⊆ {1, …, ℓ(g)}`.
2. **Extensions.** If `1 -> K -> G -> Q -> 1` with `K, Q ∈ 𝒩_τ`, then `G ∈ 𝒩_τ`. The class is also closed under
   subgroups and under finite-index overgroups.
3. **Geometry.** Every group acting properly and cocompactly by isometries on a CAT(0) space lies in `𝒩_τ`.
   So do every hyperbolic group and every finitely generated linear group.
4. **Splittings.** If `Λ` acts on a tree with vertex stabilizers in `𝒩_τ`, finitely many edge orbits, and
   finite relative root primes (`finite-root-prime-splittings-never-create-z-semilocal`), then `Λ ∈ 𝒩_τ`.

## Proof

**1.** An `n`-th root `h` of an elliptic `g` is elliptic, since a power of a hyperbolic element is hyperbolic.
So `h` fixes some `w`, and then `g = h^n` fixes `w`, so `h ∈ Stab(w)` with `w ∈ Fix(g)`. The converse inclusion
is trivial. For hyperbolic `g`, use `ℓ(h^n) = n ℓ(h)` with `ℓ(h) >= 1`.

**2.** Let `h^n = g ≠ 1`, and write bars for images in `Q`.
- **If `ḡ ≠ 1`:** `n ∈ R_Q(ḡ)`.
- **If `ḡ = 1`:** `h̄` has finite order `k | n`, with primes in `τ(Q)`. Then `h^k ∈ K` and `(h^k)^(n/k) = g`, so
  `n/k ∈ R_K(g)`.
- **Either way,** the primes of `n` lie in a finite set depending only on `g`.
- **Torsion.** An element of prime order `p` maps to an element of order `p` or to `1`, so
  `τ(G) ⊆ τ(K) ∪ τ(Q)`.
- **Subgroups** are immediate.
- **Finite-index overgroups** are extensions of a normal core in `𝒩_τ` by a finite group, and finite groups
  lie in `𝒩_τ`.

**3.** Let the action on the CAT(0) space `X` be proper and cocompact.
- **Hyperbolic elements.** Every element is semisimple, and the translation lengths of hyperbolic elements
  form a discrete set bounded below by some `ε > 0` (Bridson–Haefliger II.6.10, recalled). A root of a
  hyperbolic `g` is hyperbolic, so `n ≤ ℓ(g)/ε`.
- **Elliptic elements.** These have finite order, and `G` has finitely many conjugacy classes of finite
  subgroups (Bridson–Haefliger II.2.8, recalled). So the orders of torsion elements are bounded. That bounds
  `τ(G)` and the roots of elliptic elements.
- **Hyperbolic groups.** Stable translation lengths of infinite-order elements are bounded below, and there
  are finitely many conjugacy classes of finite subgroups (standard).
- **Linear groups.** For infinite-order elements this is `fg-linear-groups-have-roots-at-finitely-many-primes`.
  - *Characteristic 0.* Torsion orders are bounded by Selberg's lemma.
  - *Characteristic p.* Elements of finite order prime to `p` are semisimple, with root-of-unity eigenvalues in
    a finitely generated field, so their orders are bounded. Unipotent orders are bounded by the dimension.

**4.** Finite-order elements are elliptic, so `τ(Λ)` is the union of the `τ` of the vertex groups. The root
bound is part 2 of the splitting node. ∎

## Census: one irreducible piece (route (a) of the coordinator)

Each entry says whether a finitely presented residually finite group of that kind can contain `Z_(S)`.

| candidate | verdict | reason |
|---|---|---|
| RF irreducible lattices in products of trees (Wise, Rattaggi, Kimberley–Robertson, Janzen–Wise) | **no** | They act geometrically on a CAT(0) square complex (item 3), whether linear or not. |
| lattices in exotic `Ã₂` and other Euclidean buildings | **no** | CAT(0) (item 3). |
| non-linear RF hyperbolic groups (e.g. Canary–Stover–Tsouvalas, arXiv:2207.14356) | **no** | Hyperbolic (item 3). |
| Deligne-type central extensions `1 -> Z -> Γ̃ -> Γ -> 1` of lattices, and every extension of a lattice by an `𝒩_τ` kernel | **no** | Item 2. Lattices are linear or CAT(0). Deligne's own `Sp̃_2n(Z)` is not RF anyway. |
| free-by-cyclic groups, mapping tori of free-group endomorphisms (Borisov–Sapir), GBS and tubular groups | **no** | Splitting node. |
| RAAGs, finite-type Artin and braid groups, `Aut` of f.g. nilpotent groups | **no** | Linear. |
| closed 3-manifold groups | **no** (*sketch*) | JSJ pieces are hyperbolic, or Seifert (central extensions of orbifold groups, item 2). Edge groups are root-closed peripheral `Z²`, so `ρ = ∅`. |
| mapping class groups `MCG(S)` | **no** (*sketch*) | Penner's lower bound on pseudo-Anosov dilatations bounds roots of pA pieces. Roots preserve the canonical reduction system, and fractional twists have denominators bounded by torsion orders. |
| `Out(F_n)`, `Aut(F_n)` | **no** (*sketch*) | Growth rates of exponential strata are weak Perron numbers of bounded degree, so they are bounded away from 1. Polynomial parts are handled via UPG theory. `Aut(F_n)` then follows from `Out(F_n)` by item 2, since `Inn ≅ F_n` and `Out(F_n)` is virtually torsion-free. |
| automaton groups, contracting and Röver–Nekrashevych envelopes | **no** (translation type) | `automaton-groups-see-only-smooth-periods` (bh-free-16). |
| KMS soluble groups | **no** | `kms-minsky-groups-contain-no-z-localized`. |
| **characteristic-0 soluble KMS-type overgroups of the Euler lamplighter `G_l`** | **open** | Not extension-built from `𝒩_τ` pieces: `G_l` itself is abelian-by-(`Z ≀ Z`) with a non-finitely-generated `Z_(l)` kernel. |
| **Steinberg and elementary groups over finitely presented rings** (`St_N(R_l)`) | **open, conditional** | The `K_2` corner symbols must be killed without losing `Z_(l)`. |

**Reading.** Every finitely presented residually finite group on the standard lists is in `𝒩_τ`, except the two
open rows.
- **What item 2 forces.** For every normal subgroup `N` of a witness `G`, either `N` or `G/N` lies outside
  `𝒩_τ`.
- **What the open rows do.** Both put the divisibility into an abelian normal subgroup that is **not finitely
  generated**:
  - it is finitely generated as a module over the rest;
  - the rest acts on it with infinitely many independent eigenvalues, as the `β_k` do on `G_l`.
- **What is not proved.** That every witness has this shape.

## Route (b), briefly

- **Infinitely root-deficient edges exist, even over CAT(0) linear vertex groups.** Let `π: F_2 -> Q` with `Q`
  finitely presented. The fibre product `H_π ≤ F_2 × F_2` is then finitely generated. For `v = (a, 1)`, the
  relative root index `j_(H_π)(v)` is the order of `π(a)`, so `ρ(F_2 × F_2, H_π) ⊇ τ(Q)`.
- **Doubles never create roots.** By item 1, a double `B *_H B` gives each `g ∈ H` the root set `R_B(g)`: every
  transport of `g` is a `B`-conjugate of `g`. Only genuine transports can create roots: amalgams with different
  sides, or HNN extensions whose transports `g, φ(g), φ²(g), …` gain new root primes.
- **Where this lands.** The known criteria for residual finiteness of such HNN extensions ask for `H_π` to be
  separable. `H_π` contains the kernel `N × N` of `F_2 × F_2 -> Q × Q`, so it is separable iff the diagonal of
  `Q × Q` is, i.e. iff `Q` is residually finite. So route (b) through Mihailova edges needs a finitely presented residually finite `Q` with torsion of
  infinitely many prime orders. That is the torsion twin **T-(SL)**, open, and excluded from the same classes by
  items 2–3.

## Lesson for general BH

**Roots at infinitely many primes cannot be assembled from anything finitely generated and tame.**
- **Assembly steps:** splittings with finite relative root primes, extensions, and finite-index steps.
- **Tame starting pieces:** CAT(0), hyperbolic, linear, metabelian, KMS, automaton, MCG-like.
- **What it takes.** The divisibility of `Z_(S)` must live in a non-finitely-generated abelian normal subgroup,
  on which the rest of the group acts with infinitely many independent eigenvalues: the Euler-lamplighter
  mechanism, or its ring analogue.
- **Where to look.** The (SL) search space for `GL_n(Q)` is exactly finitely presented residually finite
  overgroups of such module extensions. That is the characteristic-0 KMS problem, or the `K_2`-repaired ring
  problem. Nothing geometric can help.
