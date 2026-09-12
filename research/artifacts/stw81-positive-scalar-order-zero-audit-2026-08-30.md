# Audit: positive scalar one-colour rigidity

Date: 2026-08-30

Claim: `stw81-positive-scalar-order-zero-approximation-is-scalar`.

1. The order comparison `phi psi(1)<=phi(1)` uses only
   `psi(1)<=1_F` and positivity.  Approximation to `c1` therefore makes the
   order-zero support `q=phi(1)` invertible.

2. For an order-zero map, the supporting homomorphism normally lies in a
   multiplier or bidual algebra.  Invertibility of `q` puts it in `D`
   explicitly as `q^(-1)phi(.)`, and its support projection is one, so the
   homomorphism is unital.

3. A unital finite-dimensional image in a projectionless algebra is
   scalar.  Every non-scalar finite-dimensional quotient contains a
   nontrivial projection, whose image would be a nontrivial projection of
   `D`.

4. The scalar functional `omega` is positive, not necessarily unital.
   The unit approximation gives `omega(1)>=c-epsilon`, permitting the
   normalization in (ISC5); positivity gives the needed bound on its norm.

5. No rescaling of either c.p.c. factorization map is performed.  This is
   why the result applies to `c id_D` even for `c<1`.

Outcome: **PASS**.
