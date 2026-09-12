---
rg: 2
id: sp21-lattice-pro-p-completions-have-finite-rank
kind: claim
title: Some cocompact arithmetic Sp(2,1) lattice has finite-rank pro-p completions at every prime
distinct_from:
  sp21-lattice-has-congruence-subgroup-property: that asks for a finite congruence kernel, all primes and all finite quotients at once; this asks only that each pro-p congruence kernel be finite, is implied by it, and is not known to imply it
  sp21-lattice-few-alternating-and-large-rank-quotients: that bounds alternating and large-rank simple quotients; this concerns p-quotients, and it kills the only known mechanism that would produce infinitely many alternating quotients
  sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel: that is the established equivalence at one finite-index subgroup and one prime; this is the open assertion that the finite side holds everywhere
---

Let `Γ` be a torsion-free cocompact arithmetic lattice in `Sp(2,1)`, set up as in
`sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel`. Assert that for every
prime `p` and every finite-index `Δ <= Γ(p)`, the pro-p completion `Δ̂_p` has finite
rank.

**Equivalent form.** By `sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel`,
every pro-p congruence kernel of `Γ` is finite. This is the congruence subgroup
property at each prime, for p-quotients only.

**Payoff.** A Caprace–Kassabov transvection group `G_(F_p,e)` has an infinite-rank
pro-p completion. So this claim rules out surjections of any `Δ <= Γ(p)` onto
such groups. That is the only known mechanism giving a hyperbolic Kazhdan group
infinitely many alternating quotients (see the transvection bullet of
`sp21-lattice-few-alternating-and-large-rank-quotients`).

## Attempts

- **From the congruence subgroup property.**
  `sp21-pro-p-finite-rank-from-congruence-property` derives this claim. It is only
  as strong as that open property; Lubotzky arXiv:1105.4785 §4 says it is not
  known for any uniform `Sp(n,1)` lattice.
- **The certificate for the other side.**
  `sp21-golod-shafarevich-test-gives-infinite-pro-p-rank` refutes this claim as
  soon as one `Δ <= Γ(p)` has `dim H^2(Δ;F_p) < d_p(Δ)^2/4` with `d_p(Δ) >= 2`.
  - **Where a certificate can live.** (T) and
    `fpbs-lackenby-derived-p-series-largeness` force
    `liminf d_p(D_i)/[Δ:D_i] = 0` along every derived p-series. So a certificate
    needs sublinear mod-p `H_1` growth, with mod-p `H^2` below the square.
  - **Not excluded.** Ershov and Jaikin-Zapirain give Golod–Shafarevich Kazhdan
    groups, and `fpbs-power-p-deficiency-excludes-property-t` excludes only power
    p-deficiency.
- **Computation.** Not run. No explicit presentation of a cocompact arithmetic
  `Sp(2,1)` lattice was available here. The Kazhdan hyperbolic presentations on
  main (`GHB(7)`, Caprace–Kassabov) are not arithmetic `Sp(2,1)` lattices, so
  p-quotient data for them says nothing about this claim.
- **Betti numbers do not decide it.**
  - The real `b_2(Δ)/[Γ:Δ]` tends to `0` along residual chains, because the
    L²-Betti numbers of `Sp(2,1)` vanish outside degree `4`.
  - Everything therefore hinges on p-torsion growth in `H_1(Δ;Z)` along towers,
    which nothing in Cairn controls.
  - Serre's rank-one philosophy predicts failure of the full congruence subgroup
    property. It does not predict which primes carry the kernel.
