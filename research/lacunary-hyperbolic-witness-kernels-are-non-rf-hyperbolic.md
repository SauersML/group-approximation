---
rg: 2
id: lacunary-hyperbolic-witness-kernels-are-non-rf-hyperbolic
kind: claim
title: A lacunary hyperbolic group is hyperbolic or has unbounded relation gaps, so a lacunary hyperbolic kernel of a finitely presented mapping torus is hyperbolic, and every such witness kernel is a torsion-free non-residually-finite hyperbolic Kazhdan group
distinct_from:
  relation-gaps-forbid-fp-mapping-tori: that proves the gap lemma and derives unbounded gaps only from a graded small cancellation presentation over the presenting generators; this derives them from one R-tree asymptotic cone, a quasi-isometry invariant that needs no presentation, and adds the hyperbolic conclusion in the finitely presented case.
  hyperbolic-rf-gives-torsion-free-lef-quotientless-kazhdan: that turns residual finiteness of hyperbolic groups into a LEF quotientless Kazhdan kernel candidate; this shows that no lacunary hyperbolic candidate of that kind can carry a finitely presented torus, and that a lacunary hyperbolic witness kernel refutes residual finiteness of hyperbolic groups.
  sofic-hyperbolic-stages-give-quotientless-kazhdan-monster: that builds kernels as limits of hyperbolic stages; this kills every such limit whose hyperbolicity constants are little-o of the injectivity radii, unless the limit is itself hyperbolic.
  finite-outer-order-radical-witnesses-cross-alekseev-thom: that splits witnesses into regions (AT) and (IO); this shows that a lacunary hyperbolic kernel always lands in (AT), as a hyperbolic group.
artifacts:
  - research/lacunary-hyperbolic-witness-kernels-are-non-rf-hyperbolic-proof.md
  - research/oos-lacunary-hyperbolic-short-relator-stages.md
  - research/relation-gaps-forbid-fp-mapping-tori.md
  - research/mapping-torus-mf-radical-lies-in-finite-residual.md
  - research/finitely-presented-lef-groups-are-residually-finite.md
  - research/fp-mapping-torus-iff-finite-automorphic-presentation.md
---

**ESTABLISHED.** Proof: `lacunary-hyperbolic-witness-kernels-are-non-rf-hyperbolic-proof`.
Its prerequisites are:
- the verbatim OOS import `oos-lacunary-hyperbolic-short-relator-stages`;
- the established `relation-gaps-forbid-fp-mapping-tori` (Parts A and B);
- `mapping-torus-mf-radical-lies-in-finite-residual`;
- `finitely-presented-lef-groups-are-residually-finite`;
- `fp-mapping-torus-iff-finite-automorphic-presentation`.

Notation is that of `relation-gaps-forbid-fp-mapping-tori`: `K = F(S)/N`, and `N_{≤R}` is the
normal closure of the relations of length at most `R`.

## Theorem

**1 (dichotomy).** Let `K = ⟨S⟩` be lacunary hyperbolic, with `S` the finite generating set of an
R-tree asymptotic cone. Then either `K` is hyperbolic, or `K` has unbounded relation gaps (UG)
over `S`. More precisely, there are scales `ℓ_k → ∞` with

```text
N_{≤ C_2 k ℓ_k} = N_{≤ ℓ_k}     for all k ≥ 1/C_2,                 (LHG)
```

and `K` is finitely presented, hence hyperbolic, exactly when these truncations are eventually `N`.

**2 (tori and split extensions).** Let `K` be lacunary hyperbolic and `H` finitely presented,
and let `φ: H → Aut(K)` be any action. If `K ⋊_φ H` is finitely presented, then `K` is a
finitely presented hyperbolic group. In particular, a mapping torus `K ⋊_ψ Z` of a
non-hyperbolic lacunary hyperbolic group is never finitely presented, for any `ψ`.

**3 (flagship witnesses).** Let `(G, K)` witness `torsion-free-sofic-exact-mf-radical-over-z`,
and suppose `K` is quasi-isometric to a lacunary hyperbolic group. Then `K` is:
- nontrivial, finitely presented, word-hyperbolic and torsion-free;
- sofic and Kazhdan;
- without nontrivial finite quotients.

So `K` is a torsion-free hyperbolic group that is not residually finite, which settles
`torsion-free-non-residually-finite-hyperbolic-group` and hence
`non-residually-finite-hyperbolic-group`. It is also a finitely presented sofic Kazhdan group that
is not residually finite, which answers Alekseev--Thom 6.1
(`fp-sofic-kazhdan-group-not-residually-finite`). The witness lies in region (AT), never (IO).

**4 (the automorphic branch).** Let `(K, φ)` satisfy (P1) and (P2) of
`automorphic-sofic-kazhdan-kernel-with-full-mf-radical`, with `K` lacunary hyperbolic. Then `K`
is a finitely presented torsion-free hyperbolic Kazhdan group without finite quotients. So no
lacunary hyperbolic group realises the intended infinitely presented (IO-int) design.

**5 (the LEF branch, unconditional).** No solution of (LK1)-(LK3) in
`torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical` has a kernel quasi-isometric to
a lacunary hyperbolic group.

**6 (conditional kill).** If every hyperbolic group is residually finite, or if every finitely
presented sofic Kazhdan group is residually finite, then:
- no witness of the flagship has a kernel quasi-isometric to a lacunary hyperbolic group;
- no (P1)+(P2) pair has a lacunary hyperbolic kernel.
