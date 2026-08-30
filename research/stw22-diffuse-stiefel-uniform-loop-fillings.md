---
rg: 2
id: stw22-diffuse-stiefel-uniform-loop-fillings
kind: claim
title: Diffuse finite-factor Stiefel spaces have a factor-uniform small-loop filling modulus
distinct_from:
  stw22-matrix-weighted-copy-uniform-loop-fillings: that theorem proves the matrix case and transfers it to arbitrary positive weights and copy numbers; the present theorem supplies the missing spectral-capture argument for projection weights in diffuse factors.
  stw22-strong-stiefel-spaces-have-uniform-loop-fillings: that theorem uses the nonexpansive Popa--Takesaki contraction in the hyperfinite factor; the present theorem works in every separable II_1 factor by localizing the defect before using an uncontrolled contraction.
artifacts:
  - research/artifacts/stw22-diffuse-spectral-capture-audit-2026-08-30.md
---

Let `(N,tau)` be a `II_1` factor. The following continuous spectral-capture
lemma holds with a universal constant. If `q in N` is a projection and

```text
x:S^1 -> Nq
```

is `2`-norm continuous with `sup_z||x(z)||_2<=delta`, then, for every
`kappa>0`, there is a `2`-norm-continuous projection loop `e_z<=q`, of
constant trace, such that

```text
tau(e_z) <= 67 delta^2/kappa^2,
||x(z)(q-e_z)|| <= kappa.                              (SC)
```

If the right side of the trace estimate is at least `tau(q)`, one may take
`e_z=q`.

Consequently, for every `II_1` factor with separable predual, every
projection `q`, and

```text
St_N(q)={v in N:v^*v=q},
```

the quadratic modulus

```text
rho_St(epsilon)=min(epsilon,1)^2/2560                  (DSF)
```

has the following factor-uniform property. Every loop in `St_N(q)` lying in
a `rho_St(epsilon)`-ball about one of its points fills in the concentric
`epsilon`-ball. The modulus is independent of `N` and `q`; no complement
slack is needed in a diffuse factor. Every individual `St_N(q)` is also
path connected and simply connected: lift a loop to the unitary group by
the one-dimensional Farah--Vaccaro theorem and contract it by Jekel's
Theorem A.

Together with `stw22-matrix-weighted-copy-uniform-loop-fillings`, this closes
the projection-weight Stiefel filling problem for every separable finite
factor under strict complement slack. The theorem does not by itself assert
the arbitrary-positive-weight multicopy statement in a diffuse factor: that
transfer additionally asks for a relative low-spectrum extension in the
moving complement of the chosen high-frame filling.
