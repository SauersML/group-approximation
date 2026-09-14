# sk-strong-5 proposal (RULES §6): no change to the note

Lane `sk-strong-5`, 2026-09-13. Target: main's `simple_kazhdan_sofic_group.tex`, rev2 e80dcf20ad (386 lines).

**(a) Change.** None to l.1–386.

**Considered and declined:** one sentence after Theorem 1, or in §3:
```latex
The same conclusions hold for $\EL_3\bigl((\bigotimes_{\Z}M_2(\F_2))\rtimes\Z\bigr)$, the elementary group of the
Bernoulli shift on the algebraic $\mathrm{CAR}$ algebra over $\F_2$; its finite models permute the tensor factors of
$(\F_2^2)^{\otimes N}$ cyclically.
```

**(b) Proof text.** The full proof would be about 20 lines for the identification and models, plus a citation for
simplicity. See `research/artifacts/sk-strong-5-second-family-2026-09-13.md` §2.

**(c) Length.** Declined, so +0. The sentence alone would be +3.

**(d) Reader-facing trade-off.** A second canonical example at +3 lines would add a fact the reader must trust:
simplicity of the lamplighter host, which the note does not prove. It is not stronger than Theorem 1 and not shorter, and
it answers no question the note asks. So it is declined.

The search's main output for the note is negative. No family gives a strictly shorter complete proof, and simplicity is
where the length is. The note should keep the subshift family and its direct simplicity proof, with the Stepanov
alternative it already cites.

**(e) Status.** Nodes `car-bernoulli-crossed-product-is-lamplighter-ring`,
`car-shift-el3-is-marked-limit-of-qubit-shift-sl-groups`, the route
`finite-simple-groups-converge-to-simple-kazhdan-via-car-shift`, and `finite-simple-kazhdan-limits-need-not-be-simple` are
all unreviewed and queued with sk-verify-7.
