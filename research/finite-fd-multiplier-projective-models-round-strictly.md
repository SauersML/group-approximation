---
rg: 2
id: finite-fd-multiplier-projective-models-round-strictly
kind: claim
title: If only finitely many classes are realized by finite-dimensional projective representations, projective models with cocycles tending to 1 round strictly
distinct_from:
  finite-multiplier-projective-models-round-strictly: that assumes H_1 and H_2 finite, so every pointwise-trivial class dies; this allows infinite H_1 and H_2 and uses only finiteness of the set of classes realized by exact finite-dimensional projective representations.
  isw-theorem-a-has-no-data-on-sp4-lattice: that removes the cocycle input of Ioana--Spaas--Wiersma Theorem A at Sp_4(Z); this says every exact finite-dimensional projective model with cocycles tending to 1 is a scalar gauge of a genuine representation, so no such sequence is a non-roundable asymptotic representation.
---

**ESTABLISHED (unreviewed).** Let `Γ` be a finitely generated group with `H_2(Γ;Z)`
finitely generated. Let

```text
R := { [c] ∈ H^2(Γ;T) : c is the exact 2-cocycle of some projective unitary
       representation α : Γ -> U(d), d < ∞ },
```

and assume `R` is finite. Let `α_n : Γ -> U(d_n)` satisfy

```text
α_n(g) α_n(h) = c_n(g,h) α_n(gh),     c_n ∈ Z^2(Γ;T),     c_n(g,h) -> 1 for all g,h.   (FR1)
```

Then for all large `n` there are genuine representations `π_n : Γ -> U(d_n)` of the same
dimension and scalars `β_n : Γ -> T` with `β_n -> 1` pointwise such that `α_n = β_n π_n`.
In particular `||α_n(g) - π_n(g)||_op -> 0` for every `g`, so `α_n` rounds strictly.

Derivation: `finite-fd-multiplier-projective-models-round-strictly-proof`.

**Reading.**
- **Where instability must live.** At such `Γ` a non-roundable asymptotic representation
  cannot be an exact finite-dimensional projective model with trivializing cocycles. Its
  defects must be non-scalar, or it must be only asymptotically projective, which means not
  realized exactly in finite dimensions.
- **Model tests.**
  - Finite groups: `R` is finite and the conclusion holds.
  - `Z^(2g) ⋊ Sp_(2g)(Z)`: the Heisenberg classes `exp(2πi ω(v,Aw)/k)` make `R` infinite, and
    the conclusion fails there (`rf-kazhdan-group-not-flexibly-hs-stable`). So the finiteness
    hypothesis is doing real work.
- **Instance.** `sp4-projective-models-with-cocycles-to-one-round-strictly` applies this at
  `Sp_4(Z)`, where `H_2` has rank one but `R` is finite.
