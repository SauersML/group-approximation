---
rg: 2
id: hall-type-prufer-quotients-embed-in-isolated-abels-groups
kind: claim
title: Every finitely generated subgroup of a central quotient A_n/C of the Hall–Abels triangular groups over Z[1/p] embeds in an isolated group; in particular Hall's non-residually-finite group A_3/Z lies in the isolated Abels group A_4/Z, so Cornulier–Guyot–Pitsch Question 4 holds for it while Boone–Higman for it is open
requires:
  - linear-and-metabelian-groups-embed-in-isolated-groups
  - ascending-hnn-of-isolated-groups-embed-in-isolated-groups
distinct_from:
  every-decidable-group-embeds-in-an-isolated-group: that is CGP Question 4 for all decidable groups; this answers it on the Hall–Abels central quotients, which are not residually finite and so lie outside the quasi-linear case.
  linear-and-metabelian-groups-embed-in-isolated-groups: that covers groups linear over a finite product of fields, all residually finite; this covers the non-residually-finite quotients with Prüfer centre.
  fg-soluble-minimax-groups-satisfy-boone-higman: that is the OPEN Boone–Higman statement for the whole soluble minimax class; this settles only the weaker isolated-embedding question, and only for the Hall–Abels quotients, including that node's calibration example.
  hall-quotient-avoids-v-circle-groups-and-periodic-ends: that excludes locally moving hosts (V, circle groups, periodic-end hosts) for Hall's group; this exhibits a host of a different kind, a solvable isolated group with Prüfer centre.
---

**ESTABLISHED** (lane proof, bh-free-60, 2026-09-18; elementary given the imports; not
reviewed).
- **Credit.** This is a direct consequence of Cornulier–Guyot–Pitsch §5.4, which rests on
  Hall (1961) and Abels (1979). No priority is claimed. The only new remark is that it
  answers their Question 4 for these groups.
- **Imports, read at source:** Y. de Cornulier, L. Guyot, W. Pitsch, *On the isolated
  points in the space of groups*, J. Algebra 307 (2007), arXiv:math/0511714v2, PDF read
  2026-09-18, §5.4 pp. 19–22.
  - *Definition.* "Denote by A_n ⊂ GL_n(Z[1/p]) the subgroup of upper triangular matrices
    a such that a_11 = a_nn = 1 and such that the other diagonal coefficients are
    positive." The group A_3 was "introduced by Hall [Hal61]".
  - *Centre.* The centre of `A_n` is the upper-right corner `e_1n(Z[1/p])`, and `Z` is its
    copy `e_1n(Z)`.
  - *Prop. 5.6.* "The groups A_n and A_n/Z are finitely presented for all n ≥ 4" (Abels
    for `n = 4`).
  - *Prop. 5.7.* "The groups A_n/Z are finitely discriminable for n ≥ 2. In particular,
    for n ≥ 4 these groups are infinite, solvable (3-solvable when n = 4), and isolated."
  - *Lemma 5.13* (block form). Let `H ≤ G(R)` contain `U(R)`, and let `Z ≤ V(R)` be such
    that every `x ∈ V(R) − {0}` has some `α ∈ R` with `αx ∉ Z`. Then `H/Z` is finitely
    discriminable iff the abelian group `V(R)/Z` is.
  - *Lemma 4.1.* Finitely discriminable abelian groups are the groups `F × ∏ C_(p_i^∞)`,
    with `F` finite and finitely many Prüfer factors.

## Statement

Fix a prime `p`, `n >= 2` and a subgroup `C ≤ Z(A_n) = e_1n(Z[1/p])`.
1. Every finitely generated subgroup of `A_n/C` embeds in an isolated group.
2. For `n >= 4` and nonzero cyclic `C = e_1n(cZ)`, the group `A_n/C` is itself isolated.
   For `c = 1` this is CGP Prop. 5.7.
3. **Hall's group.** `E = A_3/Z = ⟨e_12(1), e_23(1), diag(1,p,1)⟩ / e_13(Z)` is Hall's
   non-residually-finite group, the calibration example of
   `fg-soluble-minimax-groups-satisfy-boone-higman` and the group of
   `hall-quotient-avoids-v-circle-groups-and-periodic-ends`. It embeds in the isolated
   group `A_4/Z`.

By 1, the class of groups embedding in isolated groups is closed under finite products and
finite extensions (`ascending-hnn-of-isolated-groups-embed-in-isolated-groups`). So finite
products of such subgroups, for different primes, and their finite extensions also embed in
isolated groups.

## Proof

- **Corner embeddings.** For `m >= n`, let `ι: A_n → A_m` put an `n × n` matrix on the
  indices `{1, …, n−1, m}` and the identity on the others.
  - `ι` is conjugation of the block embedding `M ↦ M ⊕ I` by a permutation that preserves
    the order of `{1, …, n−1, m}`. So it is an injective homomorphism into upper
    triangular matrices.
  - Its diagonal entries are `1` at the ends and positive elsewhere, so `ι(A_n) ≤ A_m`.
  - It maps `e_1n(x)` to `e_1m(x)`. So it carries `Z(A_n)` onto `Z(A_m)`, with
    `ι^{-1}(e_1m(C)) = C`. It therefore induces an injection `A_n/C ↪ A_m/ι(C)`.
- **Item 2.** `A_n` is finitely presented (Prop. 5.6), and `C` is central and cyclic, so
  `A_n/C` is finitely presented. Apply Lemma 5.13 with blocks `(1, n−2, 1)` and
  `R = Z[1/p]`:
  - `A_n` contains `U(R)`, and `V(R) = e_1n(R)`;
  - for `x ≠ 0`, some `α = p^{-N}` has `αx ∉ cZ`;
  - `R/cZ ≅ C_(p^∞) × Z/m` (write `c = p^k m` with `p ∤ m`) is finitely discriminable by
    Lemma 4.1.

  So `A_n/C` is finitely discriminable, hence isolated (CGP Prop. 2.2).
- **Item 1, `C` cyclic and nonzero.** Take `m = max(n, 4)` in the corner embedding and
  apply item 2.
- **Item 1, `C = 1`.** `A_n` is linear, so its finitely generated subgroups are covered by
  `linear-and-metabelian-groups-embed-in-isolated-groups`.
- **Item 1, `C` not cyclic.** A subgroup of `Z[1/p]` is cyclic or of the form `mZ[1/p]`
  with `p ∤ m`. Then `A_n/C` embeds in `A_n/Z(A_n) × GL_n(Z/m)`, a group linear over a
  finite product of fields, and the linear node applies again.
  - The first factor is linear over `Q`: the adjoint action on the Lie algebra of the
    unipotent radical has kernel `Z(A_n)`.
  - The second factor is reduction modulo `m`, and `p` is a unit modulo `m`.
  - An element in the kernel of both maps is central and congruent to `0` modulo `m`, so
    it lies in `C`.
- **Item 3.** This is the case `n = 3`, `C = Z`. The three matrices generate `A_3`:
  - conjugating `e_12(1)` and `e_23(1)` by powers of `diag(1,p,1)` gives `e_12` and `e_23`
    of all of `Z[1/p]`;
  - commutators then give the corner. `∎`

## Consequences

- **Q4 has hosts of a kind BH does not yet have here.**
  - `hall-quotient-avoids-v-circle-groups-and-periodic-ends` excludes Thompson's `V`,
    circle groups and periodic-end hosts for `E`. The isolated host above is none of these.
    It is an S-arithmetic solvable group whose finite discrimination comes from the socle
    `Z/p` of its Prüfer centre.
  - This realizes the third branch of "Where the remaining room is" in Attempt 5 of
    `every-decidable-group-embeds-in-an-isolated-group`: an isolated host that is not
    locally moving.
- **Reduction for Boone–Higman.** `E ≤ A_{4,p}/Z`, so Boone–Higman for Hall's group, and
  for every finitely generated subgroup of `A_{n,p}/Z` with `n <= 4`, follows from Boone–Higman for the
  one finitely presented 3-solvable group `A_{4,p}/Z`. For larger `n`, use the increasing
  chain of the `A_{n,p}/Z`.
  - By `boone-higman-iff-isolated-hosts-and-local-boone-higman` (per-input form), this is
    one existential sentence per group.
- **The rest of the soluble minimax class.** Let `G` be finitely generated soluble minimax,
  and suppose `G/τ(G)` embeds in an isolated group. Then `G` does iff some homomorphism
  from `G` to an isolated group is injective on the Chernikov radical `τ(G)`, by item 4 of
  `ascending-hnn-of-isolated-groups-embed-in-isolated-groups`.
  - The hypothesis on `G/τ(G)` holds when `G/τ(G)` is residually finite, by
    `rf-soluble-minimax-groups-satisfy-permutational-bh`. That `G/τ(G)` is residually
    finite is standard but was not re-read.
  - The Hall–Abels groups supply such homomorphisms for the groups treated here. The
    general case is OPEN.

## Lesson for general BH

**Divisible central torsion is invisible to isolation.**
- A Prüfer centre destroys residual finiteness, and it is what blocks every locally moving
  host of Hall's group.
- Finite discrimination only asks for a finite socle that meets every normal subgroup, and
  `C_(p^∞)` has socle `Z/p`. So arithmetic hosts with Prüfer centres, S-arithmetic unipotent
  radicals made finitely presented by Abels' theorem, answer Question 4 on exactly the
  non-residually-finite soluble inputs that locally moving hosts miss.

**Consequences.**
- Question 4 and Boone–Higman diverge at central torsion. Isolated hosts may keep a centre;
  simple hosts must kill it.
- For such inputs the whole Boone–Higman problem sits in one finitely presented isolated
  group per prime, `A_{4,p}/Z`.
