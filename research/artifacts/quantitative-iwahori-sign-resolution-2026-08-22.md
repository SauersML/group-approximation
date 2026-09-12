# Quantitative Iwahori sign resolution for approximate vertices

The projective projection identity

```text
1-|tr((2P-1)U(2P-1)U^*)|^2
 =4 ||[P,U]||_2^2 (1-||[P,U]||_2^2)
```

has two zero branches.  The exact-vertex argument selects one branch by
passing to a sign character.  Canonical matrix microstates only give an
approximate vertex presentation, so the relators must be included in the
selection argument.

The finite-level repair is elementary and dimension free.  Projective energy
`e_s` gives a sign `epsilon_s` with

```text
||Ad(rho(s))(2P-1)-epsilon_s(2P-1)||_2 <= sqrt(2e_s).
```

Along a word these errors telescope linearly.  A relator with negative sign
would place the same symmetry within `L_R a` of its negative and within
`2delta` of itself, forcing `2<=L_R a+2delta`.  Below that threshold the
signs satisfy every relator exactly and hence define a genuine sign character
of the presented group.  Ordinary commutation on the Iwahori edge similarly
forces the character to be trivial on the edge.  The restriction map on
mod-two characters is injective for the modular vertex, so the character is
trivial and only the ordinary-commuting branch survives.

This closes the exact-versus-asymptotic mismatch in the route from projective
arithmetic transfer to canonical Iwahori projection transfer.  The remaining
analytic input is precisely projective commutant transfer itself.
