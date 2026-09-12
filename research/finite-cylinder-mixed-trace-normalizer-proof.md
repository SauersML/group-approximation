---
rg: 2
id: finite-cylinder-mixed-trace-normalizer-proof
kind: route
title: Decompose stabilizer characters and induce their regular cores
target: finite-cylinder-mixed-traces-kill-normalizer-holonomy
requires: []
---

Fix one orbit representative `omega`, put `K=H_omega`, and restrict the
actor representation to `V_omega=P_omega V`.  Covariance identifies the
representation over the whole orbit with `Ind_K^H(sigma)`, where
`sigma=U|_(V_omega)`.  Under the exact mixed-trace hypothesis the character
of `sigma` is zero away from the identity.  Character orthogonality gives

```text
mult_pi(sigma)
 = |K|^(-1) sum_(s in K) conjugate(chi_pi(s)) Tr(sigma(s))
 = dim(V_omega) dim(pi)/|K|.
```

These are exactly the multiplicities of a multiple of `lambda_K`.
Induction sends `lambda_K` to `lambda_H`; choosing its regular basis and
transporting it by coset representatives simultaneously makes the orbit
PVM and every actor unitary permutation-valued.  Taking the orthogonal sum
over the finitely many orbits proves the exact assertion.

If instead every nonidentity mixed normalized trace has modulus at most
`beta`, the same character formula and `|chi_pi(s)|<=dim(pi)` show that
`sigma` contains at least

```text
floor(dim(V_omega)/|K|-d beta (|K|-1)/|K|)
```

regular copies.  The omitted dimension in that orbit is at most
`|H omega|(d beta(|K|-1)+|K|)`.  Summing over orbit representatives and
using `|H omega||K|=|H|` gives the stated bound `(FCM4)`.  The transported
regular bases again preserve all atom projections, so the retained core is
simultaneously permutation-valued.

For a Bernoulli cylinder atom, Fourier expansion expresses
`tr(P_omega U_s)` as a finite linear combination of canonical traces of
lamp-actor group words.  These vanish for every nonidentity stabilizer
element, exactly supplying the hypothesis after a coherent finite actor
table has been extracted.  The displayed two-atom `C_2` representation has
zero scalar actor trace but mixed traces `+1/2` and `-1/2`, and its negative
block stays normalized-HS distance at least one from every atom-preserving
permutation.  This proves the asserted sharpness of cylinder resolution.
