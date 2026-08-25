---
rg: 2
id: state-support-corner-qwep-proof
kind: route
title: Pass QWEP through the bidual corner and Takesaki expectation
target: state-support-corner-qwep-recovers-hyperlinearity
requires:
  - state-support-corner-exactifies-near-representation
  - invariant-free-near-state-is-amenable-regular-cover
  - amenable-trace-descends-through-locally-liftable-quotient
  - hyperlinear-near-representation-criterion
---

The QWEP permanence chain is short but the distinction from WEP is crucial.

1. `B(H)` has WEP, hence QWEP.
2. A C-star algebra is QWEP if and only if its bidual is QWEP.  Therefore
   `M=B(H)**` is QWEP.  This step would be false with WEP in place of QWEP.
3. QWEP passes to von Neumann corners, so `sMs` is QWEP.
4. By `state-support-corner-exactifies-near-representation`, Takesaki's
   theorem supplies a normal conditional expectation

   ```text
   E:sMs -> N=W*(rho(G)) ~= L(G).
   ```

   The range of a conditional expectation from a QWEP C-star algebra is
   QWEP.  Hence `N` is QWEP.
5. For a finite von Neumann algebra with separable predual, QWEP is equivalent
   to Connes embeddability, with any prescribed faithful normal trace
   preserved.  Applied to the regular trace on `N`, this gives `(SCQ2)`.

For the local-lifting counterexample in the claim, use `G=F_2` and obtain a
near-state from the Kahl--Schneider equivalence.  The trace on its cover `A`
is amenable by `invariant-free-near-state-is-amenable-regular-cover`.  If the
regular quotient were locally u.c.p.-split, then
`amenable-trace-descends-through-locally-liftable-quotient` would make the
regular trace on `C*_r(F_2)` amenable.  The latter is equivalent to amenability
of `F_2`, which is false.

The injectivity and rigidity counterexamples use the same group:
`L(F_2)` is noninjective, while `F_2` has neither property `(T)` nor
property `(TT)/T`.  Thus none of those properties follows from the expected
support-corner inclusion.

Primary permanence references: Kirchberg's QWEP results (in particular,
QWEP is preserved by bidualization and relatively weakly injective/expected
subalgebras) and Ando--Haagerup--Winslow,
*Ultraproducts, QWEP von Neumann algebras, and the Effros--Marechal topology*,
arXiv:1306.0460.  The individual finite-algebra equivalence between QWEP and
trace-preserving embeddability in `R^omega` is Kirchberg's finite QWEP
criterion.
