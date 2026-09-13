---
rg: 2
id: integer-root-limits-galois-balanced-proof
kind: route
title: Serre's resultant bound for the limits, a resultant count for balance, and Smith's theorem for the atomless remainder
target: integer-root-limits-are-galois-balanced-serre-measures
requires:
  - smith-serre-measures-are-conjugate-limits
artifacts:
  - research/artifacts/determinant-integer-root-limits-2026-09-12.md
  - research/artifacts/determinant-conjecture-serre-class-2026-09-11.md
---

Artifact `determinant-integer-root-limits-2026-09-12.md`, Section 2.

**(1) ⇒ Serre inequalities (2.1).** This is the proof of
`integral-spectral-limits-satisfy-serre-inequalities`, with one change: for a
monic integer `P` with real roots and nonzero `Q in Z[x]`, the product of the
nonzero `Q(lambda)` over roots of `P` is ± the lowest nonzero coefficient of the
characteristic polynomial of `Q(companion(P))`, a nonzero integer.

**(1) ⇒ balance (2.2).** Let `alpha` be algebraic with minimal polynomial `M`.
1. Write `P_k = M^(e_k) S_k` with `M ∤ S_k`, and put `c_k = e_k deg M / deg P_k`.
   If `M` is non-monic or has a non-real root, then `e_k = 0` (Gauss's lemma;
   real roots).
2. `Res(S_k, M)` is a nonzero integer, so the roots of `S_k` put mass at most
   `log B / log(1/delta)` on `{|M| < delta}`.
3. Portmanteau on small intervals around each real root of `M` gives
   `mu({alpha_i}) = lim c_k / deg M` for every conjugate. So the conjugates carry
   equal mass, and the mass is `0` unless `alpha` is a totally real algebraic
   integer.

**(2) ⇒ (1) (2.3).** Take `Sigma = [-R, R]` containing the support, with `R > 2`.
1. **Split.** Write `mu = sum_O w_O nu_O + mu'`, balanced orbit atoms plus a
   remainder with no algebraic atoms.
2. **Kill orbits.** Apply the Serre inequality to
   `Q = Q_0^k prod_(O in F) M_O`. Orbit terms outside `F` are `>= 0` and at most
   `log ||Q||_Sigma`. Letting `k -> infinity`, then `F` exhaust the orbits, gives
   `integral log|Q_0| d mu' >= 0` for every `Q_0`.
3. **Smith.** The normalized `mu'` meets condition (1) of Smith's Theorem 1.5 on
   `Sigma`, which has capacity `R/2 > 1`
   (`smith-serre-measures-are-conjugate-limits`). So it is a limit of root
   distributions of distinct irreducible monic `R_j` with roots in `Sigma`.
4. **Mix.** Rational mixtures of finitely many orbit measures and one `nu_(R_j)`
   are root distributions of products `prod P_i^(e_i)`, and they converge to
   `mu`. QED
