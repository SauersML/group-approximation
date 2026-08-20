# Focused William Slofstra paper audit — 2026-08-20

This audit records the papers read for the active hyperlinear-group program.
It distinguishes imported theorems from ideas which remain speculative.  It
does not claim a nonhyperlinear group.

## Directly useful recent papers

### Fanizza--Kroell--Mehta--Paddock--Rochette--Slofstra--Zhao, arXiv:2510.04943v4

The paper constructs computable `L`-families of BCS algebras.  On the
nonmember side, the distinguished projection `D` satisfies a quantitative
signal-collapse estimate `phi(D)<=C_m epsilon`.  The engine is the recurrence

```text
P_n + X_n P_n X_n - P_(n+1)=0
```

with polynomial-size relator decompositions (Propositions 5.10 and 5.14),
summed against an exponentially decaying weight.  Theorem 5.5 quantitatively
flattens nested conjugacy BCS relations; Remark 5.9 gives a fixed 42-variable,
31-constraint conjugacy gadget of context size at most three.

Cairn already imports these facts in `fanizza-turing-bcs-signal-collapse` and
the fixed nonlinear-menu claims.  The new S3 radical lane now supplies a
dimension-free local payment for the nonlinear predicates.  The paper still
does not groupify the additive projection recurrence or provide a separated
group word on the nonmember side.

### Slofstra--Zhang, arXiv:2412.10305v2

Theorem 1.3 protects the exact order of the central solution-group phase from
all right-hand sides when the incidence hypergraph has degree/girth `(4,4)` or
`(3,6)` and all nonzero coefficients are non-zero-divisors modulo `p`.  The
proof turns phase collapse into a closed planar picture and rules out a
minimal picture by Euler curvature.

This suggests using a genuinely two-dimensional high-girth complex for the
S3 packet return.  The limitation is explicit: the paper does not prove an HS
stability estimate, and it leaves finite-dimensional operator solutions for
its odd-prime examples open.

### Mastel--Slofstra, arXiv:2404.00926v2

Lemma 6.6 and Corollary 6.7 show that contextwise classical transformations,
including adding private local variables without changing context overlaps,
preserve weighted BCS defect with constant one.  Theorem 7.5 shows that
bounded context subdivision preserves quantum/commuting soundness with a
polynomial loss.

This is the correct algebraic justification for placing Schur--Clifford
packet variables privately inside contexts.  It prevents the accidental
global commutation that invalidated older selector-gluing attempts.  It does
not produce scalar group relations or the recurrent return map.

### Paddock--Slofstra, arXiv:2310.07901v2

The BCS algebra organizes classical, matrix, `R^U`, and tracial
satisfiability.  Proposition 5.8 identifies the exact missing object: a
tracially satisfiable but non-`R^U` satisfiable LIN system exists exactly when
a finitely presented nonhyperlinear group exists.  This validates the BCS
source language but is an equivalence, not a compiler.

### Paddock--Slofstra--Zhao--Zhou, arXiv:2301.11291v2

Extremal full-rank correlations can be characterized as unique abstract
finite-dimensional states, and finite-dimensional self-testing agrees between
tensor-product and commuting models under the paper's hypotheses.  The paper
explicitly does not address robust self-testing.  Therefore it cannot by
itself supply the normalized-HS modulus needed for packet return.

## Older structural papers re-read for the active bottleneck

### Slofstra, arXiv:1806.05267v1

The group contains an infinite Clifford family, a shift `z`, and an HNN
compressor `t z t^-1=z^2`; the latter addresses `x_(2^k)` by a word of length
`O(k)`.  Quantitative Higman embedding gives polynomial area control, and
Gowers--Hatami exactification turns a separated central sign into the robust
capacity bound `d>=2^(floor(n/2)-1)`.  This is the established model for
compact addressing plus finite-packet exactification.  It makes required
dimension grow extremely fast but never forces `d>=F(d)>d` inside the same
model.

### Slofstra--Vidick, arXiv:1711.10676; Slofstra, arXiv:1703.08618 and 1606.03140

These papers connect group hyperlinear profile to entanglement, demonstrate
nonclosure of finite-dimensional quantum correlations, and embed finitely
presented groups into solution groups.  Two warnings remain load-bearing:
nonattainment of a perfect finite-dimensional strategy is not a constant
soundness gap, and the universal solution-group embedding is not by itself a
quantitative normalized-HS compiler.

## Resulting research direction

The best synthesis is now narrower than “combine all of MIPstar with a
Turing-machine group”:

```text
Fanizza polynomial doubling recurrence
  + private-context weighted soundness
  + S3-equivariant fixed-scale radical payment
  + a high-girth two-dimensional return complex
  + a separate separated Boone/self-referential mark.
```

All local finite algebra and local HS payment are present.  The remaining
theorem is quantitative stability of the two-dimensional return: exact
picture curvature must be upgraded to a dimension-free HS energy inequality.
