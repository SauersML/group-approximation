---
rg: 2
id: klingen-twisted-fibres-all-fail-llp
kind: claim
title: Every Packer-Raeburn fibre C*(Z^2 x| SL_2(Z), sigma_t) of the Klingen extension of Sp4(Z) fails the local lifting property
distinct_from:
  klingen-rational-twisted-fibres-fail-llp: that gives, at rational t only, a conditional expectation onto an untwisted copy of C*(Z^2 x| SL_2(Z)); this proves failure of the LLP at every real t, including irrational t, where no finite-index subgroup kills the twist.
  klingen-central-quotient-is-min-inexact: that is inexactness of 0 -> I_t -> C*(E) -> A_t -> 0 after tensoring with B(l^2); this is failure of the LLP of the quotient A_t itself.
  sp4-mod3-twisted-fibres-have-llp: that is the mu_3-twisted algebra of the whole lattice Sp_4(Z); this is about twisted algebras of the Klingen quotient Z^2 x| SL_2(Z) by the long-root centre.
  twisted-c-star-opposite-inverts-cocycle: that is a general identification of the opposite algebra of a twisted group C*-algebra; this is a non-LLP statement for one explicit family of twists.
  sp2g-z-full-c-star-algebra-has-llp: this closes every fibrewise-permanence route through the Klingen subgroup; it does not decide the root.
artifacts:
  - research/artifacts/klingen-central-quotient-2026-09-16.md
---

**CLAIM.**  Let `Lambda = Z^2 x| SL_2(Z)`, with `(v,g)(w,h) = (v + g w, g h)`.  Let
`c((v,g),(w,h)) = omega(v, g w)` be the integer 2-cocycle of Ioana–Spaas–Wiersma
(arXiv:2006.01874, proof of Corollary B), where
`omega((a,b),(a',b')) = ab' - ba'`.  For `t in R` put
`sigma_t = exp(2 pi i t c)`.  Then:

```text
for EVERY t in R, the full twisted group C*-algebra A_t = C^*(Lambda, sigma_t)
does not have the local lifting property.
```

**Context.**

- `A_t` is the fibre at `e^{2 pi i t}` of the `C(T)`-algebra `C^*(E)`, where
  `E = Z x_c Lambda` is the Klingen subgroup `{N(v,c) L(g)}` of `Sp_4(Z)`
  (`klingen-central-quotient-is-min-inexact`; artifact §0, §1).
- Equivalently, `A_t` is the full crossed product of the rotation algebra
  `A_{2t}` by the canonical `SL_2(Z)`-action on its Weyl generators (artifact
  §4A, remarks).  At `t = 0` the claim is ISW Corollary B for `Z^2 x| SL_2(Z)`.

**Proof idea** (artifact §4A, Theorem 3).  This is the twisted form of ISW's
second proof of Theorem A.

1. Choose rationals `s_n -> t` with `0 < |s_n - t| < 1/2`.  Reducing `E` modulo
   the denominator of `s_n` gives finite-dimensional `sigma_{s_n}`-projective
   representations `pi_n` of `Lambda`.
2. **min.**  `W_u (x) conj(pi_n)` has cocycle `sigma_{t - s_n}`, whose
   antisymmetrization on `Z^2` is `e^{4 pi i (t - s_n)} != 1`.  So ISW's Claim
   `gap` (relative (T) of `(Lambda, Z^2)` via NPS) bounds the min norm of
   `y = sum_i W_t(g_i) (x) (conj pi_n(g_i))_n` by `D < m`.
3. **max.**  Since `sigma_{s_n} -> sigma_t` pointwise, `x -> [(pi_n(x) (x) 1)_n]`
   is an exact `sigma_t`-representation in `prod_n (M_{d_n} (x) M_{d_n}) / c_0`.
   It commutes with `b -> [(1 (x) b_n)_n]`.  The maximally entangled vectors give
   `||y||_max >= m`.
4. Transfer to `B(l^2)` by the block-diagonal conditional expectation, and apply
   Kirchberg's criterion.

**Consequences.**

- Every fibre of the `C(T)`-algebra `C^*(E)` fails the LLP.  So no
  fibrewise-permanence argument can certify the LLP for `C^*(E)`, and hence none
  can certify it for `C^*(Sp_4(Z))`, which contains `C^*(E)` with a conditional
  expectation.  Examples are Farah–Fritz–Winter arXiv:2603.18456v2,
  Corollary `c ext`, or any variant with a dense set of good fibres.
- If `C^*(Sp_4(Z))` has the LLP, then so does `C^*(E)`.  Then:
  - every central quotient `C^*(E) -> A_t` is min-inexact against `B(l^2)`
    (artifact Lemma A).  This does hold, unconditionally, by
    `klingen-central-quotient-is-min-inexact`;
  - at every point of `T`, the LLP of `C^*(E)` needs norm inflow from
    neighbouring fibres (artifact §5, R1).
