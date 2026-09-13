---
rg: 2
id: finite-multiplier-projective-models-round-strictly
kind: claim
title: When H_1 and H_2 are finite, every projective model with cocycles tending to 1 rounds strictly in operator norm
distinct_from:
  sp4-metaplectic-class-pointwise-coboundary-limit: that proves coboundaries are pointwise closed, so one fixed nonzero class is never a pointwise limit of coboundaries; this proves that when H_1 and H_2 are finite, every pointwise-trivial sequence of cocycles is eventually a coboundary, and that the models round strictly.
  sp4-fd-projective-multiplier-is-finite: that bounds the finite-dimensionally realizable scalar classes of Sp_4(Z), whose H_2 has rank one; this treats groups with finite H_2, where every realizable class tending to zero dies, and derives same-dimension rounding.
  rf-kazhdan-group-not-flexibly-hs-stable: that exhibits non-roundable projective models on a Kazhdan group with a non-torsion H^2 class; this shows such models always round once H_1 and H_2 are finite.
---

**ESTABLISHED (unreviewed).** Let `Γ` be a finitely generated group with `H_1(Γ;Z)` and
`H_2(Γ;Z)` finite. Let `α_n : Γ -> U(d_n)` satisfy

```text
α_n(g) α_n(h) = c_n(g,h) α_n(gh),     c_n ∈ Z^2(Γ,T),     c_n(g,h) -> 1 for all g,h.
```

Then there are genuine representations `π_n : Γ -> U(d_n)` of the same dimension, and scalars
`β_n : Γ -> T` with `β_n -> 1` pointwise, such that `α_n = β_n π_n` for all large `n`. In
particular `||α_n(g) - π_n(g)||_op -> 0` for every `g`.

Derivation: `finite-multiplier-projective-models-round-strictly-proof`.

**What it rules out.**
- **ISW Theorem A.** At such `Γ`, Ioana--Spaas--Wiersma Theorem A (arXiv:2006.01874v2) has no
  input for any subgroup `Λ`. Its hypotheses (1) and (2) for cocycles on the whole group are
  incompatible: a coboundary on `Γ` restricts to a coboundary on `Λ`.
  - The LLP failures ISW obtain for `SL_n(Z)`, `n >= 3`, come from a subgroup by heredity.
  - Hilbert--Schmidt instability does not pass from a subgroup to the ambient group, so their
    method gives no instability of the ambient group there.
- **Central extensions.** If `Γ` is perfect with finite `H_2`, then
  `H^2(Γ;A) = Hom(H_2(Γ;Z),A) = 0` for every torsion-free abelian `A`. Every central extension
  by `A` therefore splits, and Dogon's Theorem 1.3 (arXiv:2211.10492v3, "non-split central
  extension" by a torsion-free `A`) has no input.
- **Where instability must live.** At such `Γ`, a non-roundable asymptotic representation must
  have genuinely non-scalar defects. Weil-type, theta-type and all other asymptotically
  projective models round.

**Model tests.**
- **The unstable instance fails the hypothesis.** `Z^(2g) ⋊ Sp_(2g)(Z)` has a free summand in
  `H_2`, and there the conclusion fails (`rf-kazhdan-group-not-flexibly-hs-stable`).
- **A group satisfying it.** Finite groups satisfy the hypothesis and the conclusion holds.

**Instance for the Kun--Thom vertex (hypothesis named, not verified here).**
- `Γ = EL_r(F_q[x_1..x_d])` with `r >= 3` is perfect, since `e_ij(a) = [e_ik(a), e_kj(1)]`.
- The theorem applies whenever its Schur multiplier `H_2(Γ;Z)` is finite. For `r` in the
  stable range this multiplier should be `K_2(F_q[x_1..x_d]) = K_2(F_q) = 0`, by homotopy
  invariance and Quillen.
- Those K-theory inputs are not source-verified in this lane.
