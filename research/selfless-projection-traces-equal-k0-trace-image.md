---
rg: 2
id: selfless-projection-traces-equal-k0-trace-image
kind: claim
title: In a selfless tracial C*-algebra the projection traces are exactly the K_0 trace values in [0,1], so for torsion-free selfless groups Kadison--Kaplansky is the trace conjecture
distinct_from:
  fractional-matrix-trace-gives-projection-in-g-star-z: that realizes matrix traces by projections after passing from G to G * Z; this realizes every K_0 trace value in [0,1] on the group itself, whenever its reduced algebra is selfless, and records the selfless hosts.
  robert-tracial-selfless-regularity: that gives strict comparison and stable rank one; this consumes strict comparison to compute the set of projection traces.
  unconditional-spectra-of-kk-witnesses-cross-the-gap: that gives integer traces for idempotents of unconditional completions on torsion-free Lie subgroups; this shows that on the same groups a Kadison--Kaplansky witness is exactly a class of K_0(C*_r) of non-integer trace.
---

**ESTABLISHED** by `selfless-projection-traces-equal-k0-trace-image-proof`.

**Lemma.** Let `A` be unital with faithful tracial state `τ`, and suppose `(A, τ)` is selfless. Then

```text
{ τ(e) : e a projection of A }  =  τ_*(K_0(A)) ∩ [0,1],
```

and every `x ∈ K_0(A)` with `τ_*(x) ∈ (0,1)` is the class of a projection of `A`.

**Selfless group algebras `(C*_r Γ, τ)`**, all already imported on main:
1. `Γ = G * H` with `G, H` nontrivial and not both `C_2`
   (`non-dihedral-free-products-are-completely-selfless`);
2. `Γ` acylindrically hyperbolic with trivial finite radical (`ozawa-php-groups-completely-selfless`);
3. `Γ` Zariski-dense in `PSL(d,R)`, `d >= 2`, for example every finite-index subgroup of `SL_3(Z)`
   (`zariski-dense-psl-subgroups-are-completely-selfless`);
4. `Γ` a nontrivial linear group with trivial amenable radical (`vigdorovich-linear-selflessness`).

**Corollary (one group at a time).** Let `Γ` be torsion-free and in one of the classes 1--4. Then
`C*_r(Γ)` has no projection other than `0` and `1` iff `τ_*(K_0(C*_r Γ)) ⊆ Z`. A matrix witness
over `Γ` is already a `1x1` witness over `Γ`; there is no need to pass to `Γ * Z`.

**Instance: torsion-free finite-index subgroups of `SL_3(Z)`, such as `Γ(3)`.**
Kadison--Kaplansky for `Γ(3)` is equivalent to integrality of `τ_*` on all of
`K_0(C*_r Γ(3))`. Main knows integrality on two parts only:
- the assembly image (`assembly-image-traces-are-integral-for-torsion-free-groups`);
- the image of `K_0` of every unconditional completion
  (`unconditional-spectra-of-kk-witnesses-cross-the-gap`, item 1).

So a witness on `Γ(3)` is exactly a class of `K_0(C*_r Γ(3))` of non-integer trace. Such a class
lies outside both images.

**Non-vacuity.**
- The hypothesis fails on real objects: `C*_r(D_∞)` and `C*_r` of any nontrivial abelian group are
  not simple, hence not selfless.
- It holds on real objects, for example `C*_r(F_2)`.
- The conclusion carries content already with torsion. In `C*_r(C_2 * C_3) = C*_r(PSL_2(Z))`,
  `[(1 + a)/2] - [(1 + b + b^2)/3]` has trace `1/6`, so the lemma produces a projection of trace
  `1/6`, which is not a subgroup average.

**Novelty.** Not claimed for the lemma: it is the standard consequence of strict comparison, as
in Dykema--Rørdam (GAFA 1998) for nuclear free products. The per-group corollaries on classes
2--4 were not found stated in a bounded search (2026-09-12).
