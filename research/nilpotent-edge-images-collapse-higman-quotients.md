---
rg: 2
id: nilpotent-edge-images-collapse-higman-quotients
kind: claim
title: In a nontrivial quotient of Higman's group neither opposite pair generates a virtually nilpotent, or virtually solvable finite-rank, group, so tree actions with such edge stabilizers have a global fixed point
distinct_from:
  almost-commuting-opposite-higman-generators-force-collapse: that kills quotients in which a and c (almost) commute, the abelian case; this kills every virtually nilpotent image of <a,c> or <b,d>, of any class, by a Hirsch-length eigenvector count.
  nontrivial-higman-quotients-are-not-locally-elementary-amenable: that forbids homomorphisms from a quotient to elementary amenable or residually finite targets; this constrains a subgroup of the quotient, the image of an opposite pair, which receives no homomorphism from the quotient.
  nonsofic-subgroups-of-higman-group-have-free-edge-groups: that concerns subgroups of H4 itself and its two fixed splittings; this concerns arbitrary nontrivial quotients and arbitrary actions of them on trees.
artifacts:
  - experiments/higman-edge-collapse-2026-09-17/README.md
---

**ESTABLISHED** by `higman-nilpotent-edge-collapse-proof`.

**Statement.** Let `Q` be a quotient of
`H4 = < a, b, c, d | b^a = b^2, c^b = c^2, d^c = d^2, a^d = a^2 >` (`x^y = y^-1 x y`).

1. **Nilpotent edge images collapse.** If the image of `<a,c>` in `Q`, or the image of `<b,d>`,
   is virtually nilpotent, then `Q = 1`. More generally, `Q = 1` as soon as the subgroup
   `<c^(a^k) : k >= 0>` lies in a subgroup of `Q` that is virtually solvable of finite Hirsch length
   (torsion-free rank). This covers, for example, virtually polycyclic groups and `BS(1,n)`.
2. **Tree gate.** Let `Q` act on a tree without inversions. Every generator is elliptic, and either
   `Q` fixes a vertex, or some edge is fixed by all of `a, c`, or some edge is fixed by all of `b, d`.
3. **Consequence.** If `Q != 1` acts on a tree without inversions and every edge stabilizer is
   virtually nilpotent, or virtually solvable of finite Hirsch length, then `Q` fixes a vertex. In particular a nontrivial quotient of `H4` is never a
   nontrivial amalgam or HNN extension over such subgroups.

**What it kills.** Attempt 5 of `higman-group-is-sofic` asked for a sofic quotient of `G_1 = <a,b,c>` in
which `F_ac` has an amenable image `A`, glued to its relabelled copy over `A`. The glued group is a
quotient of `H4` in which `<a,c>` has image `A`. By item 1 the glued group is trivial whenever `A` is
virtually nilpotent or virtually solvable of finite rank. By items 2–3, the same holds for any construction of a nontrivial sofic quotient as
a tree of groups over virtually nilpotent edge groups, at any depth where the Higman generators act.
Only amenable edge images of infinite Hirsch length remain, such as infinite-rank metabelian groups
(`Z wr Z`-like) or non-elementary amenable groups.

**Key identity.** `b a^k = a^k b^(2^k)`, hence `u_k = c^(a^k)` satisfies `u_k^(b^(2^K)) = u_k^(2^(2^(K-k)))`
for `0 <= k <= K`. A single conjugation therefore scales `K+1` infinite-order elements of the
edge image by `K+1` distinct exponents. In a nilpotent group of Hirsch length `h` their Mal'cev logarithms
are eigenvectors with distinct eigenvalues, which is impossible for `K >= h`. In the solvable case the
same count runs on the rationalised derived-series factors.

**Computer cross-checks (independent of the proof).** GAP coset enumeration shows that `H4` plus any
one of the following relator sets defines the trivial group:
- `[a,c]`;
- `[[a,c],a], [[a,c],c]` (class 2);
- `(ac)^2`;
- `[a,c^2]`;
- `[a^2,c^2]`.

The class-3 and metabelian relator sets exceeded `2*10^6` cosets. See
`experiments/higman-edge-collapse-2026-09-17/README.md`.
