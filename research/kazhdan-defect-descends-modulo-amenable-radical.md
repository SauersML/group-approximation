---
rg: 2
id: kazhdan-defect-descends-modulo-amenable-radical
kind: claim
title: A quotientless Kazhdan kernel is saturated by a compression defect exactly when the defect's image saturates the kernel modulo any invariant amenable normal subgroup, so KCF modulo the amenable radical kills (EK1)
distinct_from:
  abelian-extensions-kill-kcf-compression-defects: that kills the defect when the kernel itself is KCF; this pushes the defect to the quotient of the kernel by an invariant amenable normal subgroup, so the kernel only needs to be KCF modulo its amenable radical, and it adds the converse saturation criterion and the lifting class.
  locally-residually-finite-targets-kill-compression-defects: that kills the image of the defect in a locally residually finite target and says nothing about the kernel of the map; this uses property (T) and the absence of finite quotients to recover all of the kernel from its image modulo an amenable subgroup.
  finite-rank-kernel-forces-abelian-defect-subgroups: that absorbs normal defect subgroups into a finite-rank linear kernel; this is linear-free and absorbs the amenable part of the kernel into the defect itself.
  locally-rf-by-amenable-cannot-supply-exact-kazhdan-kernel: that forbids Kazhdan subgroups of locally-RF-by-amenable groups; this is about amenable normal subgroups inside the kernel, which that statement does not see.
  kazhdan-rational-relation-cover-reduction: that builds torsion-free quotientless Kazhdan groups as abelian extensions K of Q and says nothing about (EK1); this computes (EK1) on such extensions from Q and gives the root gate for the induced envelope.
  mapping-torus-mf-radical-descends-through-kernel-radical: that pulls the MF radical back from the mapping torus of the MF quotient; this pulls the compression defect back from the mapping torus of the quotient by an amenable normal subgroup, with no MF radical involved.
artifacts:
  - research/kazhdan-defect-descends-modulo-amenable-radical-proof.md
  - research/abelian-extensions-kill-kcf-compression-defects.md
  - research/kazhdan-rational-relation-cover-reduction.md
---

**ESTABLISHED.** Use the intrinsic compression-centralizer defect of
`abelian-extensions-kill-kcf-compression-defects`:

```text
Comp_G(L) = { s : s L s^-1 <= L },   G_comp(L) = <Comp_G(L)>,
D_G(L)    = << [g z g^-1, l] : g in G_comp(L), z in C_G(L), l in L >>_G .
```

Let `K` be a Kazhdan group with no nontrivial finite quotient, `phi in Aut(K)`,
`G = K semidirectProduct_phi Z`, and let `A <= K` be a `phi`-invariant amenable
normal subgroup of `K`, for example the amenable radical `Rad_amen(K)`, which is
characteristic. Put `pi : G -> Gbar = (K/A) semidirectProduct Z`. Then for every
subgroup `L <= G`:

```text
(AD1)  pi(D_G(L)) <= D_Gbar(pi L),   and  D_G(L) <= K x {0}  when L is Kazhdan;
(AD2)  D_G(L) = K x {0}  iff  pi(D_G(L)) = K/A;
(AD3)  if K/A is KCF (C(Lambda) = 1 for every nontrivial Kazhdan Lambda <= K/A),
       then D_G(L) <= A < K for every Kazhdan L; so (EK1) fails, unless K = 1.
```

When `A` is characteristic, for example `Rad_amen(K)` or `Z(K)`, (AD3) holds for
every `phi`.

Torsion-freeness is used nowhere in (AD1)-(AD3).

**Lifting class.** Let `A` be abelian. Take `Lbar <= Gbar` and `cbar in
C_Gbar(Lbar)`, let `L <= G` be a subgroup with `pi(L) = Lbar`, and let `c` be
any lift of `cbar`. Then

```text
f_c(l) = c l c^-1 l^-1  in A,     f_c in Z^1(L; A)   (L acts on A by conjugation),
(AD4)  some lift of cbar centralizes L   iff   [f_c] = 0 in H^1(L; A).
```

In particular every lift of a root acts trivially on `L cap A`.

**Root gate for torsion-free kernels.** Let `K` be torsion-free and `A` abelian.
Suppose `pi(L)` contains a nontrivial element of finite order. Then:

- `L cap A != 1`;
- every `z in C_G(L)` fixes a nonzero element of `A`.

Now suppose in addition that `A` embeds `K/A`-equivariantly into an induced module
`(+)_{q in K/A} W`. This is clause 2 of
`relation-cover-rational-lifting-over-quotientless-kazhdan`, the envelope that gives
soficity in `kazhdan-rational-relation-cover-reduction`. Then

```text
(AD5)  every root z in C_K(L) of Z-degree 0 has pi(z) of finite order in K/A.
```

## What this changes for (EK1)

1. **Saturation lives modulo amenable radicals.** A witness `(K,phi,L)` of (EK1)
   gives the saturated defect `D_Gbar(pi L) = K/A` in the mapping torus of
   `K/A`, for every invariant amenable `A`. This includes `K/Rad_amen(K)`, a
   quotientless Kazhdan group with trivial amenable radical. That quotient may
   have torsion and need not be sofic, so saturation and torsion-freeness come
   apart across amenable extensions. Conversely, any configuration in `G` whose
   descended defect saturates `K/A` satisfies (EK1).
2. **The KCF biography gets stronger.** A witness kernel is not KCF even modulo
   amenable radical, nor modulo any invariant amenable normal subgroup. This kills
   every quotientless Kazhdan kernel that is an amenable extension of a KCF group,
   for example a central or abelian extension. It holds for every automorphism
   preserving the extension kernel. When the quotient has no nontrivial amenable
   normal subgroup, that kernel is `Rad_amen(K)`, so the kill holds for every
   automorphism; this is the case for simple non-amenable quotients and for
   torsion-free non-elementary hyperbolic quotients. That covers:
   - amenable extensions of Titz Mite--Witzel lattices, including every
     rational relation cover `[P/R_sat, P/R_sat]` over them;
   - amenable extensions of torsion-free hyperbolic or 2-dimensional CAT(0)
     Kazhdan groups.

   So the relation-cover machine cannot repair the soficity gap of Titz--Witzel
   kernels for (EK1).
3. **A decomposition of (EK1) on the relation-cover route.** For
   `K = P/R_sat ->> Q` with torsion-free abelian kernel `A`, (EK1) splits into two
   prerequisites that can each fail on their own:
   - (Sat) a descended configuration in `Q semidirectProduct Z` whose defect
     normal closure is `Q`. This fails when `Q/Rad_amen(Q)` is KCF.
   - (Lift) a Kazhdan `L <= K` over the descended source, a compressor lift, and
     roots with vanishing class in `H^1(L; A)`. This fails at (AD5) for degree-0
     roots of infinite order whenever `pi(L)` has torsion and the envelope is
     induced.

   On the natural choice `Q = EL_3(LC(X,F_q) semidirect Z)`, every root subgroup
   has order `p`. So a source containing a root element forces every degree-0
   root to be torsion modulo `A`. The scalar and diagonal roots of infinite order
   in the ring recipes (`simple-ring-centralizer-compression-gives-xmf`,
   `xmf-via-matricial-compression-ring-proof`) can lift only with nonzero
   `Z`-degree.

Proof: `kazhdan-defect-descends-modulo-amenable-radical-proof`.
