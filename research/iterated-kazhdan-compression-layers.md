---
rg: 2
id: iterated-kazhdan-compression-layers
kind: claim
title: MF radicals absorb successive Kazhdan compression layers in quotient towers
artifacts:
  - GroupApproximation/Sofic/KazhdanCompressionLayers.lean
  - GroupApproximation/Endpoint/ApproximationRadicals.lean
---

# MF radicals from successive quotient layers

Let

```text
W --stage 0--> V₀ --step 0--> V₁ --step 1--> V₂ --> ...
```

be a commuting tower of surjections.  Suppose the initial stage kernel lies in
the MF radical of `W`.  At stage `n`, suppose there is a compression core
`Cₙ` in `Vₙ` and a normal subgroup `Kₙ ◁ Vₙ` such that

```text
Kₙ has property (T),
Kₙ ≤ defect(Cₙ),
ker(step n) ≤ Kₙ.
```

Then every stage kernel lies in the MF radical of `W`:

```text
ker(stage n) ≤ Rad_MF(W)                         for every n.   (1)
```

The point is that the analytic theorem is applied separately in each quotient.
It gives

```text
Kₙ ≤ Rad_MF(Vₙ).
```

Once `ker(stage n) ≤ Rad_MF(W)` is known, the radical pullback identity gives

```text
Rad_MF(W) = stage(n)⁻¹(Rad_MF(Vₙ)).              (2)
```

Since `ker(step n)` is contained in the radical on the right, its preimage is
contained in the radical on the left.  This is precisely the kernel of the
next stage.  Induction proves (1).

## Two endpoints

If every element of `W` is killed at some finite stage, then

```text
Rad_MF(W) = W.                                     (3)
```

No individual stage has to kill all of `W`.  The successive layers may be
small, and the union of their pullbacks may have no Kazhdan property of its
own.

More generally, let `W --> P` be a surjective limit map whose kernel is the
union of the finite-stage kernels.  If `P` is MF, then

```text
Rad_MF(W) = ker(W --> P).                          (4)
```

Thus the tower does not merely prove non-MF behavior: it computes the universal
MF-visible quotient exactly.

## Structural consequence

The one-step form is already useful.  If `φ : E --> Q` is onto,
`ker φ ≤ Rad_MF(E)`, and a normal Kazhdan subgroup `K ◁ Q` lies in a compression
defect in `Q`, then

```text
φ⁻¹(K) ≤ Rad_MF(E).                                (5)
```

In particular, if the compression defect is all of `Q` and `Q` has property
`(T)`, then `Rad_MF(E)=E`.  The source `E` need not have property `(T)`.

Equations (1)--(5) are formalized in
`GroupApproximation/Sofic/KazhdanCompressionLayers.lean` and re-exported by
`GroupApproximation/Endpoint/ApproximationRadicals.lean`.
