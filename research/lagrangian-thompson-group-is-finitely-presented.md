---
rg: 2
id: lagrangian-thompson-group-is-finitely-presented
kind: claim
title: For some odd n >= 3 the odometer Lagrangian Thompson group is finitely presented and its commutator subgroup is simple and contains Deligne's lattice
distinct_from:
  lagrangian-thompson-group-contains-deligne-lattice: that constructs the host and proves the containment; this is the open finiteness and simplicity question, which would give Boone-Higman for Deligne's lattice at odd n.
  deligne-lattice-satisfies-boone-higman: that is the embedding question for Deligne's lattice (stated there for Sp_4, n = 2, "any n >= 2 behaves the same"); this is one sufficient host at odd n >= 3.
  perfect-decidable-inputs-have-fp-shell-envelopes: that asks finite presentation of shell envelopes, where Kazhdan inputs sit in a germ group; here the Kazhdan lattice acts without virtual fixed points, which is a different regime (deligne-lift-actions-are-not-almost-v).
---

**OPEN.** Let `n ≥ 3` be odd, and let `V_Λ^τ` be the group of
`lagrangian-thompson-group-contains-deligne-lattice`: the topological full group of
`O_τ × (PSp_{2n}(Z) ⋉ Y_Λ)` on `Z_2 × Y_Λ`, where `Y_Λ` is the Maslov Cantorization of
the real Lagrangian Grassmannian. The claim is that for some such `n`:
- `V_Λ^τ` is finitely presented;
- its commutator subgroup `D(V_Λ^τ)` is simple;
- `D(V_Λ^τ)` contains the image of Deligne's lattice `Γ̃`.

**Consequence.** Deligne's lattice for `Sp_{2n}(Z)`, `n` odd, would embed in a
finitely presented simple group, since a finite-index subgroup of a finitely
presented group is finitely presented. For the case `n = 2` of
`deligne-lattice-satisfies-boone-higman`, the even-`n` variant with a sphere factor
would be needed (scope of the containment node).

## Attempts

1. **Known finiteness engines do not apply (established).**
   - By `deligne-lift-actions-are-not-almost-v`, neither `PSp_{2n}(Z)` on `Y_Λ` nor
     `Γ̃` on `Z_2 × Y_Λ` is almost-V. So Belk–Hyde–Matucci Theorem 2.1 over `V` cannot
     certify this group.
   - Groups of local similarities with a finite similarity structure are Haagerup
     (Hughes; not read at source), so the Farley–Hughes `F_∞` theorem cannot apply.
   - The self-similar and higher-rank-graph criteria (Li; Matui for shifts of finite
     type; Nekrashevych for contracting groups) need a finite-state coding of the
     action. Whether `PSp_{2n}(Z)` acts on `Y_Λ` by a finite-state coding is not known
     here.
2. **Naive Farey combinatorics fails for `n ≥ 2` (lane remark).**
   - For `n = 1`, finite presentation of `V` rests on three facts. `PSL_2(Z)` acts
     simply transitively on oriented Farey edges. The two cells cut by an edge are
     rigid, with trivial stabilizer. Each cell subdivides canonically at the mediant.
   - For `n ≥ 2`, `Sp_{2n}(Z)` still acts transitively on ordered unimodular
     transverse pairs `(L, L')`, with `L ⊕ L' = Z^{2n}` on integer points. These
     correspond to symplectic bases up to `GL_n(Z)` (textbook).
   - Their Maslov cycles cut `Λ` into `n + 1` cells, the signature classes of
     invertible symmetric matrices in the chart transverse to `L'`.
   - But the stabilizer of the pair and the positive cell contains `GL_n(Z)/±1`,
     acting by `S ↦ A S A^T`. That is infinite, so cells are not rigid.
   - The "mediants" (unimodular positive forms `A A^T`) form one infinite
     `GL_n(Z)`-orbit. So no finite, canonical subdivision rule of Thompson type exists
     on these cells.
   - A Brown-criterion proof would have to use an arrangement complex whose vertex
     stabilizers contain arithmetic groups such as `GL_n(Z) ⋉ Sym_n(Z)`. These are
     finitely presented, so the stabilizers are not the obstacle. Such a proof would
     also need finitely many orbits of arrangements in each filtration level. Pairs of
     rational Lagrangians already fall into infinitely many `Sp_{2n}(Z)`-orbits,
     distinguished by the elementary divisors of the pair. Restricting to unimodular
     ("Farey") arrangements is the natural repair. Whether their cells generate the
     topology of `Y_Λ`, and whether the resulting complex is highly connected, is
     untested.
3. **Candidate structure for a real proof (untested).**
   - Voronoi reduction theory gives a `GL_n(Z)`-invariant polyhedral tessellation of
     the positive cone with finitely many orbits of cells (textbook).
   - Combining Voronoi cells inside each signature cell with unimodular Maslov pairs
     is a candidate "Lagrangian Farey tessellation" with finitely many
     `Sp_{2n}(Z)`-types.
   - If it has a finite subdivision rule, a Stein–Farley-type complex might work,
     with arithmetic vertex stabilizers in place of finite ones.
   - This is the step that would make `V_Λ^τ` a Thompson group, and it is the open
     core.
4. **Simplicity and containment for a variant (2026-09-18, lane `bh-free-55`;
   established there).**
   - In `deligne-lattice-in-fg-simple-lagrangian-brin-thompson-group`, the odometer
     groupoid `O_τ` is replaced by the Cuntz groupoid `G_2`.
     - The center then acts through any infinite-order element of `V`.
     - For even `n`, a factor `F_3^{2n} ∖ {0}` carries the central involution.
     - `Y_Λ` is replaced by the unimodular Cantorization of
       `unimodular-maslov-cantorization-is-minimal-expansive`.
   - For that host, and every `n ≥ 2`, the commutator subgroup is simple and finitely
     generated and contains `Γ̃`. So only finite presentation is left, in
     `lagrangian-brin-thompson-group-is-finitely-presented`.
   - For `V_Λ^τ` itself, the same proof gives two things:
     - minimality, local contraction and topological freeness of `Y_Λ` (item 8 of the
       Cantorization node);
     - `Γ̃ ≤ D(V_Λ^τ)`, by the diagonal trick: `Γ̃^{ab}` is finite by (T), and the
       Cuntz part of `O_τ` makes `m` disjoint copies.
   - Hence `D(V_Λ^τ)` is simple, provided `O_τ` is minimal, effective and purely
     infinite. This proviso is not rechecked here.
   - Finite generation of `D(V_Λ^τ)` would need expansivity of `Y_Λ`. That is not
     known; it is known for `Y_u`.
