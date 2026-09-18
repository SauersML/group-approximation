---
rg: 2
id: amenable-free-top-syzygy-forces-type-fp
kind: claim
title: A group of cd n with vanishing top L2-Betti number whose top syzygy over a finite free (n-1)-truncated resolution is free is of type FL; in dimension 2 Kropholler's question is equivalent to every finitely generated amenable cd-2 group having an aspherical presentation on finitely many generators
distinct_from:
  amenable-fp-iff-affiliated-top-homology-vanishes: that shows type FP is equivalent to vanishing of H_{n-1}(G; U); this uses the vanishing of H_n(G; U), which is automatic for amenable groups, and turns it into a bound on the rank of any free top syzygy, so non-FP_2 is pushed into the non-freeness of one projective module
  top-homology-of-free-complex-carries-wall-obstruction: that concerns cocompact free complexes and the Wall obstruction of a finitely generated projective; here the top syzygy is not finitely generated, and the obstruction is L2-smallness of a free module
  cd-two-kazhdan-kernel-with-grigorchuk-quotient: that Ollivier-Wise group has an aspherical infinite presentation on finitely many generators; item 3 here shows no amenable group of cd 2 other than BS(1,m) can have one, and item 4 computes that its second L2-Betti number is infinite
  rn-cd-two-group-has-gd-two-iff-cockcroft-presentation: that shows an FP_2 non-fp cd-2 group needs infinitely many 1-cells in any aspherical 2-complex, and characterises gd 2 by Cockcroft presentations under residual nilpotence; this shows an amenable non-FP_2 cd-2 group admits no aspherical 2-complex with finite 1-skeleton at all, using L2-dimension instead of Cockcroft counts
  amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical: that constrains the normal subgroups of a two-dimensional counterexample; this constrains its presentations and its second syzygy module
---

**ESTABLISHED** through `amenable-free-top-syzygy-forces-type-fp-proof`, from
`amenable-fp-iff-affiliated-top-homology-vanishes` (its imports (J1)-(J3), (J6) and item 4) and
Lyndon's asphericity theorem for torsion-free one-relator presentations.

`U = U(G)` is the algebra of affiliated operators, `H_q(G; U) = Tor_q^{Z[G]}(U, Z)`.

1. **Free top syzygies are finitely generated.** Let `n >= 1`, `cd_Z G = n`, and
   `0 → P → F_{n-1} → … → F_0 → Z → 0` a resolution with `F_0, …, F_{n-1}` finitely generated
   free and `P` projective. Suppose `b_n^(2)(G) = dim_U H_n(G; U) = 0`; this holds for every
   infinite amenable `G`. If `P` is free, then `rank P <= rank F_{n-1}`. So `G` is of type `FL`.
   More generally, every free direct summand `F` of `P` has `rank F <= rank F_{n-1}`.
2. **Geometric form.** If such a `G` has an `n`-dimensional `K(G,1)` complex whose
   `(n-1)`-skeleton is finite, then the complex is finite. No finiteness of the `n`-cells is
   assumed.
3. **Dimension 2.** Let `G` be a finitely generated amenable group of cd 2 that is not `BS(1,m)`,
   that is, a two-dimensional counterexample to Kropholler's question. Fix generators
   `x_1, …, x_d` and let `P = ker(Z[G]^d → Z[G], e_j ↦ x_j − 1)`, a projective module.
   - (a) `P` is not free, and every free direct summand of `P` has rank at most `d − 2`.
   - (b) `G` has no aspherical presentation `⟨x_1, …, x_d | R⟩` on finitely many generators, with
     `R` of any cardinality. `G` is not the fundamental group of any aspherical 2-complex with
     finitely many 0-cells and 1-cells.
   - (c) **Equivalence.** Kropholler's question for groups of cd at most 2 is equivalent to each of:
     - (F) every finitely generated amenable group of cd 2 has, for some finite generating set, a
       free second syzygy `P`;
     - (Asph) every finitely generated amenable group of cd 2 has an aspherical presentation on
       finitely many generators.
4. **Calibration.** Any group `Γ` with an aspherical presentation on `d` generators and infinitely
   many relators has `b_2^(2)(Γ) = ∞`. This holds for the Ollivier–Wise group over the Grigorchuk
   group in `cd-two-kazhdan-kernel-with-grigorchuk-quotient`.

**What it kills.** Every construction of a two-dimensional counterexample that comes with an
aspherical presentation on finitely many generators and infinitely many relators is dead. The
exact step where it fails: the kernel of the second boundary map over `U(G)` has dimension at least
`|R_0| − d` for every finite `R_0 ⊆ R`, whereas amenability makes it zero. The asphericity inputs
below are recalled, not re-checked. This covers:

- infinitely presented `C'(1/6)`, `C(6)` and `C(4)–T(4)` small-cancellation groups, with no
  relator a proper power and no two relators conjugate up to inversion. These presentations are
  aspherical (Chiswell–Collins–Huebschmann, Math. Z. 178 (1981));
- graphical `C(6)` / `C'(1/6)` limits over a finite generating set, whenever the coned-off
  complex is aspherical (Gruber). Replacing each cone on a finite graph by 2-cells along a basis of
  fundamental cycles gives a homotopy-equivalent complex with one vertex and finitely many
  1-cells;
- Rips and Ollivier–Wise type constructions, whose presentations are `C'(1/6)`;
- more generally, any 2-complex with finite 1-skeleton and contractible universal cover, such as
  a quotient of a CAT(0) square or polygonal complex by a free action with finitely many orbits of
  vertices and edges.

A two-dimensional counterexample has geometric dimension 2 only through 2-complexes with
infinitely many 1-cells, or geometric dimension 3, which would also be an Eilenberg–Ganea
counterexample.

**What this leaves.** The obstruction for a counterexample sits in one module: a countably
generated projective `P ≤ Z[G]^d` that is not finitely generated, is not free, and is `L²`-small,
in the sense that `U ⊗ P` embeds in `U^d`. By the Eilenberg swindle, `P ⊕ Z[G]^(∞)` is free.
Statement (F) is a Bass-type "big projective modules are free" statement for `Z[G]`: it asks that
non-finitely-generated syzygies be free. Bass's theorem (Illinois J. Math. 7 (1963)) gives
freeness over connected commutative noetherian rings. `Z[G]` is neither commutative nor
noetherian, and item 1 shows that any freeness theorem for `Z[G]` must fail for `L²`-small
projectives. So a proof of (F) would need an input that sees the difference between `L²`-small
and `L²`-big projectives.
