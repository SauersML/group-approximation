---
rg: 2
id: radu-mark-survives-only-if-horizontal-group-embeds
kind: claim
title: A quotient of Radu's BMW lattice keeps the mark (xz)^4 only if its kernel meets no vertex stabilizer of the vertical tree, so <a,b,c> embeds and no amenable quotient keeps the mark
distinct_from:
  radu-mark-survives-only-in-non-rf-split-quotients: that constrains mark-keeping quotients whose kernel maps onto a finite-index subgroup of Q, through the slab sign character, and needs the normal subgroup theorem for Q to reach amenable quotients; this shows that the kernel of any mark-keeping quotient meets no vertex stabilizer of T_v, with no hypothesis on the quotient.
  radu-mark-is-controlled-by-one-commutator: that bounds the mark by one commutator (Radu's Lemma 3.5) in almost actions; this makes that commutator vanish exactly, from one kernel element fixing a vertex of T_v.
  radu-bmw-lattice-embeds-in-titz-witzel-kernel: that imports non-residual finiteness, whose proof puts xz into the image of <a,b,c> using finiteness of the quotient; this gets the same inclusion from any nontrivial vertex-fixing kernel element.
artifacts:
  - research/artifacts/radu-mark-elliptic-check.py
  - research/artifacts/radu-mark-elliptic-check-output-2026-09-13.txt
---

**ESTABLISHED (unreviewed).** Let

```text
Γ_R = <a,b,c,x,y,z | a^2,b^2,c^2,x^2,y^2,z^2, axax, ayay, azbz, bxbx, bycy, cxcz>
```

be Radu's BMW lattice (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`), `C = <a,b,c>`,
`V = <x,y,z>`, `δ = xz`, and let `T_v = Γ_R/C` be the vertical tree, with base vertex `o = C`
and the neighbours of `gC` being `gxC, gyC, gzC`. The vertex stabilizers of `T_v` are the
conjugates of `C`. Let `N ◁ Γ_R`.

1. **Elliptic kernel elements kill the mark.** If some element of `N` fixes a vertex of `T_v`
   and acts nontrivially on `T_v`, then `xz ∈ C·N` and `(xz)^4 ∈ N`.
2. **Faithfulness.** `Γ_R` acts faithfully on `T_v`.
3. **Mark-keeping quotients.** If `(xz)^4 ∉ N`, then `N ∩ gCg^(−1) = 1` for every `g ∈ Γ_R`.
   So `N` acts freely on the vertices of `T_v`, and `C ≅ C_2 * C_2 * C_2` embeds in `Γ_R/N`.
   In particular `Γ_R/N` contains a nonabelian free group.
4. **Amenable quotients.** No amenable quotient of `Γ_R` keeps the mark. More generally, no
   quotient without nonabelian free subgroups keeps it. So `Γ_R` is not residually amenable, and,
   being finitely presented, it is not locally embeddable into amenable groups. This refutes
   `radu-lattice-residually-amenable-at-the-mark`, and residual amenability cannot certify
   `radu-bmw-lattice-sofic`. Neither the normal subgroup theorem for `Q`
   (`radu-arithmetic-quotient-normal-subgroups-finite-or-finite-index`) nor the structure theorem
   `radu-mark-survives-only-in-non-rf-split-quotients` is used.

**Reading.** Radu's proof that the mark lies in the finite residual (arXiv:1712.01091,
Proposition `33nonrf`, source read on MSI) has two steps:
* In a finite quotient, a kernel element fixing the ball `B(o,1)` acts nontrivially on `T_v`, and
  the local action of `C` then puts `xz` into the image of `C`.
* The image of `C` normalizes `<u>`, `u = y(xz)^2y`, through a sign, so `[u, xz]` or `[u, xzb]`
  vanishes, and Lemma 3.5 kills the mark.

Only the first step uses finiteness, and all it needs is one nontrivial elliptic element in the
kernel. An amenable quotient supplies one, because `C` is not amenable and `C` acts faithfully on
`T_v`.

**Calibration.**
* The groups `Γ_R/γ_k(Λ_v)` of `radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups` keep the
  mark. Their kernels lie in the free kernel `Λ_v`, which acts freely on `T_v`, as item 3 requires.
* In a finite quotient `C ∩ N ≠ 1`, so item 3 recovers Radu's non-residual finiteness at the mark.

**Scope.** The mechanism is Radu's. The observation that its finite step needs only an elliptic
kernel element, and the amenable consequence, were not found in the sources read (Radu,
arXiv:1712.01091 §5; Titz Mite–Witzel 3.4–3.6 as recorded in
`research/artifacts/titz-witzel-radu-sublattice-2026-09-11.md`). No wider literature search; no
novelty is claimed.

Proof in `radu-mark-horizontal-embedding-proof`.
