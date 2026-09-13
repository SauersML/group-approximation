---
rg: 2
id: sl3z-abelian-lambda-labellings-round-to-flat-ones
kind: claim
title: Near-flat labellings of finite SL3(Z)-sets with values in a torsion-free abelian group round to flat ones, by property (T)
distinct_from:
  sl3z-lambda-almost-cocycles-round-to-flat-ones: that is the rounding claim DTR for a general finitely generated Λ in SL3(R), open; this proves DTR when the labels lie in a torsion-free abelian subgroup, so abelian flux tubes cannot refute it
---

**ESTABLISHED (unreviewed).** Notation as in `sl3z-lambda-almost-cocycles-round-to-flat-ones`: `Γ = SL_3(Z)`
with its Steinberg generators `S`, a finite presentation `⟨S | R⟩`, finite `Γ`-sets `V`, labellings
`λ : V × S → Λ`, relator cells, flatness, and the budget

```text
cost(λ, λ')  =  #{(v,s) : λ' != λ}  +  Σ_(λ' != λ) log( ||λ'(v,s)|| · ||λ'(v,s)^(−1)|| ).
```

**Theorem.** Let `A <= SL_3(R)` be a finitely generated torsion-free abelian subgroup, so `A ≅ Z^r`. For every
finite `Σ ⊂ A` there is `f_Σ : (0,1] → [0,∞)` with `f_Σ(δ) → 0` as `δ → 0`, such that for every finite `Γ`-set
`V` (transitive or not) and every `λ : V × S → Σ` with at most `δ|V|` non-flat cells, there is a flat
`λ' : V × S → A` with `cost(λ, λ') <= f_Σ(δ)|V|`. Moreover `λ'` is a coboundary, `λ'(v,s) = F(sv) − F(v)` in
additive notation for some `F : V → A`.

**Consequence for DTR.** A flat `A`-valued labelling is also flat as a `Λ`-valued labelling, for any
`Λ >= A`, and the budget does not depend on `Λ`. So a labelling whose values all lie in one torsion-free abelian subgroup
of `Λ` satisfies DTR. This covers powers of a single R-regular element of a cocompact lattice, or the labels
of a periodic Cartan flat. The flux-tube picture from `sl3z-lambda-almost-cocycles-round-to-flat-ones`
(winding along the exponentially distorted unipotent subgroup, with the flux compensated in thin
vortex tubes) is therefore not a counterexample mechanism when the flux is abelian. Any refutation of
DTR has to use labels that do not commute.

**Where (T) enters.** In one place: the Loeb-limit cocycle is a coboundary with square-integrable potential,
by Delorme–Guichardet (recalled). The integrality of the potential uses that `A` is torsion-free. For
finite or torsion coefficients, as in cosystolic expansion with `Z/2`, nothing here applies.

Proof in `sl3z-abelian-lambda-labellings-round-to-flat-ones-proof`.
