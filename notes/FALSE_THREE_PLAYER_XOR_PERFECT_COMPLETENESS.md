# Three-player XOR does not bypass perfect completeness

Date: 2026-08-13

## Outcome

The earlier reduction from constant-answer games to three-player XOR games
does not supply the missing perfect-completeness LCS theorem. It uses the
same noisy long-code mechanism as the later two-player construction.

Vidick's Theorem 4.8 takes parameters `epsilon,delta,gamma>0` and produces a
three-player XOR game `G_tilde` with

```text
omega(G'')=1       => omega(G_tilde)>=1-epsilon,       (TXP1)
omega_q(G'')<=1-gamma
                    => omega_q(G_tilde)<=(1+delta)/2.  (TXP2)
```

The completeness loss in `(TXP1)` is literal. The verifier samples a noise
function `mu` whose value is `-1` independently with probability `epsilon`.
For the honest long-code answers, acceptance occurs exactly when
`mu(x)=1`, hence with probability `1-epsilon`.

The soundness proof cannot be specialized to `epsilon=0`. Its extraction
bound has the form

```text
omega_q(G^(tensor K)) >= 8 epsilon^3 delta^4.           (TXP3)
```

At `epsilon=0`, `(TXP3)` is vacuous. Thus deleting the noise gives perfect
completeness but removes the only estimate that recovers a strategy for the
source game.

A three-player XOR predicate is indeed a linear equation among three
commuting player observables, so a **perfect-completeness** RE-hard reduction
of this form would feed a solution-group construction. The published
reduction does not have that property. The erratum to the paper additionally
invalidates the original global hardness theorem because of a separate
low-degree-test soundness error; Taller--Vidick only invoke the surviving
reduction idea, whose imperfect completeness is explicit above.

## References

- T. Vidick, *Three-player entangled XOR games are NP-hard to approximate*,
  SIAM J. Comput. 45 (2016), Theorem 4.8 and Claim 4.9.
- T. Vidick, erratum, SIAM J. Comput. 49 (2020), 1423--1427.
- A. Taller and T. Vidick, *Approximating the quantum value of an LCS game
  is RE-hard*, arXiv:2507.22444v2, Introduction.
