---
rg: 2
id: jnvwy-compute-sampler-has-nonlinear-role-marginal
kind: claim
title: The unchanged JNVWY ComputeSampler has a nonlinear role marginal
distinct_from:
  jnvwy-canonical-halt-strategy-is-affine-unsafe: that follows one chosen completeness strategy through the recursion and later proof systems; this is only the strategy-independent algebraic fact about the fixed sampler used by one compression.
  jnvwy-perfect-introspection-forces-full-seed-support: that forces every seed into every perfect introspection support for an arbitrary source marginal; this supplies the concrete nonlinear marginal to which that theorem applies.
  revealing-cl-controls-breaks-compression: that audits a proposed control-revelation repair; this leaves the published sampler unchanged and exhibits its nonlinear triple.
---

**ESTABLISHED.**  For the unchanged sampler `ComputeSampler(lambda)` of
JNVWY arXiv:2001.04383v3, Lemma 12.3, one of the two untyped role maps has
binary seeds `z_0,z_1,z_2` satisfying

```text
L(z_0)+L(z_1)+L(z_2) != L(z_0+z_1+z_2).                (CSN1)
```

The obstruction already occurs in the axis-line component of the
answer-reduction sampler.  In the notation of equation (30), that component is

```text
L_A(u,s,v)=(L^lnf_(e_(chi(s)))(u),s,0),                 (CSN2)
```

where `m=2^j>=4`, `m|q`, and `chi(s)` selects the interval of length `q/m`
containing the integer representative of `s`.  Put `s_2=q/m` in the paper's
fixed binary basis and take

```text
xi_0=0,  xi_1=(e_2,0,0),  xi_2=(0,s_2,0).              (CSN3)
```

Since `chi(0)=1`, `chi(s_2)=2`, and the canonical map
`L^lnf_(e_i)` deletes coordinate `i`,

```text
L_A(xi_1)+L_A(xi_2)=(e_2,s_2,0),
L_A(xi_1+xi_2)       =(0,s_2,0).                        (CSN4)
```

This component is a direct summand in the typed answer-reduced sampler.
Fixing one graph view that activates its type lifts the same three seeds
through detyping: three copies of the fixed binary graph prefix xor back to
that prefix.  Anchoring is handled by fixing the `Game` branch.  In parallel
repetition, vary these seeds in one coordinate and use the same seed in every
other coordinate; the repeated sampler is the direct sum of its coordinate
maps.  These operations preserve `(CSN4)` and yield `(CSN1)` for one final
untyped role map of `ComputeSampler(lambda)`.
