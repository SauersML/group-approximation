---
rg: 2
id: finite-root-prime-splittings-never-create-z-semilocal
kind: claim
title: In a group acting on a tree whose edge-in-vertex inclusions have finitely many relative root primes, every copy of Z_(S) lies in one vertex stabilizer up to those primes, and roots at infinitely many primes are never created; so no mapping torus of a free-group endomorphism and no graph of free, free abelian or nilpotent groups witnesses (SL)
distinct_from:
  end-shift-codings-of-q-inputs-need-fp-rf-semilocal-vertex-groups: its part 6 needs finite-index edge inclusions and residual finiteness; this needs only finitely many relative root primes, which also covers edge groups of infinite index (ascending HNN extensions of free groups), and uses no residual finiteness.
  bounded-valence-trees-scale-only-primes-below-the-valence: that bounds the primes that bounded valence can scale; this bounds the primes any splitting can add by an algebraic invariant of each edge inclusion, independent of valence.
  z-localized-fixes-a-vertex-or-end-of-every-tree: that allows Z_(S) to fix only an end, as an ascending union along a ray; this shows that with finitely many relative root primes P the ray carries only P-primary roots, while Z_(S ∪ P) fixes a vertex.
---

**ESTABLISHED** (lane proof; bh-invent-12, 2026-09-18; elementary Bass–Serre theory; one referee PASS with a wording fix to item 4, bh-ref-engines 2026-09-19). No priority is claimed. The statement may be folklore, but a quick literature search found it
nowhere, nor (SL) itself. Borisov–Sapir and Stallings are recalled, not re-read.

## Definitions

- **Root sets.** For a group `B` and `g ∈ B`, `R_B(g) = {n >= 1 : g = h^n for some h ∈ B}`.
  - `𝒩` is the class of groups in which every `R_B(g)`, `g ≠ 1`, involves only finitely many primes.
  - It contains every finitely generated linear group (`fg-linear-groups-have-roots-at-finitely-many-primes`)
    and every finitely generated metabelian group (`fg-metabelian-groups-have-roots-at-finitely-many-primes`).
- **Relative root primes.** For `H ≤ B`, let `ρ(B, H)` be the set of primes dividing some
  `j_H(v) = min{i >= 1 : v^i ∈ H}`, over `v ∈ B` with `⟨v⟩ ∩ H ≠ 1`.
  - `{i ∈ Z : v^i ∈ H} = j_H(v)Z`, so `v^n ∈ H` forces `j_H(v) | n`.
  - `ρ` is invariant under simultaneous conjugation.
- **For a tree.** For `Λ` acting on a tree `T` without inversions, `ρ(Λ, T)` is the union of
  `ρ(Stab(w), Stab(ε))` over all edges `ε` and endpoints `w` of `ε`. It is a finite union when there are
  finitely many edge orbits.

## Theorem

Let `Λ` act on a simplicial tree `T` without inversions, and put `P = ρ(Λ, T)`.
1. **Root transport.** Let `g ∈ Λ` fix a vertex `v`, and let `n` be coprime to every prime in `P`. Every
   `n`-th root of `g` in `Λ` lies in `Stab(v)`.
2. **Primes.** If `g` fixes `v`, every prime dividing an element of `R_Λ(g)` lies in `P` or divides an element
   of `R_(Stab v)(g)`. If `g` fixes no vertex, `R_Λ(g) ⊆ {1, …, ℓ(g)}`, where `ℓ(g)` is the translation length.
3. **Closure.** If `P` is finite and every vertex stabilizer is in `𝒩`, then `Λ ∈ 𝒩`.
4. **Z_(S).** If `P` is finite and `Z_(S) ≤ Λ` for a finite set `S` of primes, then `Z_(S ∪ P) ≤ Stab(v)` for
   some vertex `v`. `Z_(S)` itself may still fix only an end, climbing a ray by roots at primes of `P`.
   Example: the ascending HNN extension of `Z_({2})` by `x ↦ 2x` contains `Q`, which fixes only an end.
   A finite splitting with finite
   `P` contains some `Z_(S)` only if one of its vertex groups contains some `Z_(S')`.

## Proof

**1.**
- Let `h^n = g`. If `h` fixed no vertex, neither would `g = h^n`. So `h` fixes some `w`, and `g` fixes `w` too.
- `Fix(g)` is a subtree, so it contains the geodesic `v = w_0, w_1, …, w_m = w`. `g` fixes each of its edges
  `ε_i = [w_(i-1), w_i]`.
- Induct down from `w_m`, with an `h_i ∈ Stab(w_i)` satisfying `h_i^n = g` (start with `h_m = h`):
  - `h_i^n = g ∈ Stab(ε_i)`, so `j = j_(Stab ε_i)(h_i)` divides `n`;
  - the primes of `j` lie in `ρ(Stab w_i, Stab ε_i) ⊆ P`;
  - `n` is coprime to `P`, so `j = 1`, and `h_i ∈ Stab(ε_i) ⊆ Stab(w_(i-1))`. Put `h_(i-1) = h_i`.
- So `h ∈ Stab(v)`.

**2.** For the elliptic case, run the same induction for an arbitrary `n`.
- At each step `h_i^j ∈ Stab(ε_i)` and `(h_i^j)^(n/j) = g`, so the exponent drops from `n` to `n/j`.
- This writes `n = j_m ⋯ j_1 · n_0`, with every `j_i` a `P`-number and `n_0 ∈ R_(Stab v)(g)`.

For the hyperbolic case, `ℓ(h^n) = n ℓ(h)` with `ℓ(h) >= 1` for a hyperbolic `h`. If `h` fixed a vertex, so
would `g`.

**3.** This follows from 2.

**4.**
- Let `g` be the image of `1 ∈ Z_(S)`. It has `n`-th roots for infinitely many `n`, so it is elliptic by 2;
  fix `v ∈ Fix(g)`.
- For every `n` coprime to `S ∪ P`, the root `1/n ∈ Z_(S)` lies in `Stab(v)` by 1.
- These roots generate `Z_(S ∪ P)`.
- The last sentence follows by Bass–Serre theory for a finite graph of groups: `P` is then a finite union
  over edges and ends. ∎

## When P is finite

`ρ(B, H)` is finite in each of these cases, so any finite graph of groups built from them has finite `P`:
- **Finite index.** `[B : H] = d < ∞` gives `j_H(v) <= d`, by pigeonhole on the cosets `v^i H`. This recovers
  part 6 of the end-shift node without residual finiteness.
- **Free groups.** `B` is free and `H` is finitely generated. Then `j_H(v)` is at most the number of vertices
  of the Stallings core of `H`.
  - Write `v = u c u^(-1)` with `c` cyclically reduced.
  - The lift of `c^(j_H(v))` at the endpoint `q` of `u` is a cyclically reduced closed path, so it lies in the
    core.
  - Its vertices `q c^i`, for `0 <= i < j_H(v)`, are distinct.
- **Abelian groups.** `B` is finitely generated abelian and `H` is any subgroup. `j_H(v)` is the order of `v`
  in `B/H`, which divides the exponent of the torsion of `B/H`.
- **Nilpotent groups.** `B` is finitely generated nilpotent and `H` is any subgroup. `H` has finite index in
  its isolator (standard), and pigeonhole applies there.

## Instances: groups that contain no Z_(S) for any finite S

- **Mapping tori of free-group endomorphisms.** `Λ = ⟨F_r, t | t x t^(-1) = φ(x)⟩`, with `φ` an injective
  endomorphism of a finitely generated free group.
  - These are finitely presented. They are residually finite (Borisov–Sapir, Invent. Math. 160 (2005),
    341–356, recalled), and in general not linear. For example, Druţu–Sapir's non-linear
    `⟨a, t | a^(t^2) = a^2⟩` (J. Algebra 2005, recalled) is, with `b = a^t`, the group
    `⟨a, b, t | a^t = b, b^t = a^2⟩`: the mapping torus of `a ↦ b`, `b ↦ a^2` on `F(a, b)`.
  - The splitting has one vertex `F_r` and one edge, with inclusions `id` and `φ`. So
    `P = ρ(F_r, φ F_r)` is finite, and `F_r ∈ 𝒩`, so `Λ ∈ 𝒩`.
  - They are the natural "finitely presented residually finite HNN extension" candidates, and they are
    excluded, including the case `[F_r : φ F_r] = ∞`, which part 6 of the end-shift node left open.
- **Graphs of groups.** Finite graphs of groups with free vertex groups (finitely generated edge groups), or
  with finitely generated free abelian or nilpotent vertex groups (any edge groups). These include:
  generalized Baumslag–Solitar groups, tubular groups, free-by-cyclic groups, and ascending HNN extensions of
  `Z^n` and of nilpotent groups.
- **Hierarchies.** Any finite hierarchy of such splittings whose terminal pieces are finitely generated linear
  or metabelian groups, as long as every edge inclusion used has finite `ρ`.

## What an (SL) witness must contain

- **The alternative.** By part 4, a finitely presented residually finite `Λ ⊇ Z_(S)` that splits over a finite
  graph of groups contains one of two things:
  - a vertex group already containing some `Z_(S')`;
  - an edge inclusion `H ≤ B` with infinitely many relative root primes, i.e. elements `v_p ∉ H` with
    `v_p^p ∈ H` for infinitely many primes `p`.
- **Consequence.** Divisibility is born in a piece that admits no finite-`ρ` splitting, or at an infinitely
  root-deficient edge.
- **Ruled out.** The piece cannot be finitely generated linear (this covers S-arithmetic lattices), metabelian,
  a KMS group (`kms-minsky-groups-contain-no-z-localized`), or free/abelian/nilpotent. Groups acting
  geometrically on CAT(0) spaces are also out, by the same translation-length argument: translation lengths
  of hyperbolic elements are bounded below and finite subgroups have bounded order (standard, recalled).
- **What is left.** The candidates are the ones already on the board:
  - characteristic-0 soluble hosts of Euler-lamplighter type (`z-localized-embeds-in-fg-rf-soluble-group`);
  - ring groups paying in `K_2`;
  - non-affine, non-contracting self-similar groups (`odometer-root-hosts-are-non-affine-and-non-contracting`).

## Lesson for general BH

**Divisibility is splitting-rigid.**
- Roots travel along a tree only through edge inclusions. Each inclusion lets through only the primes of its
  relative root indices.
- So a tree construction with finitely many such primes creates no roots at new primes. Divisibility climbs a
  ray only at those finitely many primes, and `Z_(S ∪ P)` always sits in a vertex group.
- This makes (SL), and with it `GL_n(Q)` via every tree-type host, a question about one irreducible piece:
  - a finitely presented residually finite group that is not linear, metabelian or CAT(0)-like, and admits no
    finite-root-prime splitting;
  - or an infinitely root-deficient edge.

All the standard finitely presented residually finite constructions are excluded: HNN mapping tori
(Borisov–Sapir), graphs of free and abelian groups, and S-arithmetic lattices. The cofinite-prime arithmetic
has to be manufactured inside a single group, in the way a ring inverts all its primes at once.

## Referee (bh-ref-engines, 2026-09-19): PASS, with one overstated sentence in item 4 corrected

**Items 1–3 and item 4's main claim: correct.**
- *Item 1.* A root of an elliptic element is elliptic. `Fix(g)` contains the geodesic `[v, w]`, and
  `j_(Stab ε_i)(h)` divides `n` with primes in `P`, so it equals `1` for `n` coprime to `P`.
- *Item 2.* The exponent factorization `n = j_m⋯j_1 n_0` is correct, and `ℓ(h^n) = nℓ(h)` handles hyperbolic
  elements.
- *Item 3* follows from item 2.
- *Item 4.* The element `1` has roots at infinitely many `n`, so it is elliptic. Its roots `1/n` with `n`
  coprime to `S ∪ P` fix `v`, and they generate `Z_(S∪P)`.

**The overstated sentence is false as written.** "So a copy of `Z_(S)` is never an ascending union along a
ray" does not follow, and it fails in this example:
- Take `B = Z_({2})` (odd denominators) and `Λ = ⟨B, t | t x t^(−1) = 2x⟩`, the ascending HNN extension of `B` by `x ↦ 2x`.
- Then `P = {2}`, and `Λ ⊇ Q = Z_(∅)`.
- `Q` fixes only an end: `1/2^k` fixes `t^(−k)v` but not `v`.
- Only `Z_(∅∪P) = Z_({2}) = B` fixes a vertex.

In general `Z_(S)/Z_(S∪P)` is a sum of Prüfer groups at the primes of `P ∖ S`, and those roots may climb a
ray. The correct reading:
- the ray can only carry primes of `P`;
- the subgroup `Z_(S∪P)` always fixes a vertex.

The `distinct_from` gloss on `z-localized-fixes-a-vertex-or-end-of-every-tree` should be read the same way.
Nothing downstream changes: the (SL) alternative uses only "some vertex group contains some `Z_(S')`",
which is what is proved.
- **Corrected** (bh-invent-12, 2026-09-19): item 4, the `distinct_from` gloss and the Lesson now state the
  P-primary ray reading, with this example.

**Finite-`ρ` cases: correct.**
- Finite index: pigeonhole on `v^iH`.
- Free groups: the vertices `q c^i` are distinct, otherwise a shorter power of `v` lies in `H`.
- Abelian groups: `j` divides the torsion exponent of `B/H`.
- Nilpotent groups: the isolator is Mal'cev's, of finite index over `H`.
- The instances (mapping tori, graphs of free, abelian or nilpotent groups) follow. f.g. nilpotent groups are
  linear, so they are in `𝒩`.

**The CAT(0) remark is correct**, by semisimplicity and the discreteness of translation lengths (Bridson–Haefliger
II.6.10). Credit Mal'cev (isolators), Stallings (folding), Borisov–Sapir and Druţu–Sapir.
