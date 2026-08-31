# Audit: untwisted coefficient covariance gap

Date: 2026-08-30

Claim: `stw84-untwisted-coefficient-symbols-pay-covariance-gap`.

## Checks

1. If `e=Phi(1)` and `||e-1||=eta`, a contraction within `epsilon` of a
   unitary has both left and right Schwarz defects relative to `e` at most
   `eta+2 epsilon`.

2. The Stinespring factorization of a multiplicative defect uses one left
   and one right Schwarz defect.  Their square roots multiply to
   `sqrt((eta+2epsilon_U)(eta+2epsilon_d))`; doing this in both orders
   gives the first term of `(UCG2)`.

3. Replacing the two returned contractions by their target unitaries costs
   at most `2(epsilon_U+epsilon_d)` for the two products.  Equal errors
   therefore give the clean lower bound `epsilon>=||[U,d]||/8`.

4. Exact return of either unitary first forces `Phi(1)=1` by Schwarz and
   contractivity, then puts its source in the multiplicative domain.
   Commutation in the tensor product forces exact commutation with the
   other returned element, giving the sharper one-sided estimate.

## Boundary

The theorem concerns untwisted tensor-product symbols and u.c.p. return
maps.  It does not obstruct the coefficient crossed-product symbol, where
the defining relation is covariance rather than commutation.  Nor does it
give a lower bound for arbitrary factorizations which do not approximately
return the two generators separately.

Outcome: **PASS**.
