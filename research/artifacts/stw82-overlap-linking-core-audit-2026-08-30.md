# Audit: the multiplier-overlap linking core

Date: 2026-08-30

Claim: `stw82-overlap-is-a-full-linking-core`.

## Verified identities

1. `pAq` lies in both generated ideals: one factor is supported by `p`, the
   other by `q`.  Hence it equals the off-diagonal corner `pIq` of their
   intersection.

2. The inner-product spans are exactly `pIp` and `qIq`, not merely
   subideals.  This follows by identifying them with `pRp` and `qLq`,
   respectively.  Therefore the off-diagonal corner is a full
   imprimitivity bimodule on the overlap.

3. The Peirce matrices for `L`, `R`, and `A=L+R` have the claimed diagonal
   corners.  Adding the scalar multiplier projection changes only `pAp` to
   `pAp+C p`.

4. Since `p notin A`, `pAp+C p` is the minimal unitization of `pAp`; a
   hypothetical unit `e in pAp` would make `p-e` annihilate
   `(p-e)A(p-e)`, and essentiality of `A` in `M(A)` would force `p=e`.
   Thus no hidden extra unit is introduced.

5. Frame inner products remain in the overlap ideals.  Applying the
   quotient map proves the lower bound
   `||y-eye||>=||y+B||` exactly, so the residual-diagonal obstruction is a
   norm obstruction rather than missing bookkeeping.

## Outcome

The linking normal form and the frame firewall both **PASS**.  They do not
prove the full multiplier-projection formula.  They show precisely why two
full complementary projections on the overlap are insufficient for the
ordinary Morita-invariance argument: the off-diagonal module is full only
on the overlap, while both residual diagonal quotients can remain nonzero.
