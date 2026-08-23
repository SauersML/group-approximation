---
rg: 2
id: literal-mark-quotient-not-mf
kind: claim
title: The literal marked quotient is not MF
invalidates: [literal-quotient-computes-mf-radical, literal-mark-quotient-via-shulman-amalgam, literal-mark-quotient-via-exact-finite-models]
artifacts:
  - GroupApproximation/Sofic/LiteralSignFreeQuotient.lean
  - GroupApproximation/Endpoint/SignFreeCompressionAudit.lean
  - non_mf_groups_exist.tex
distinct_from:
  literal-mark-quotient-mf: That open claim asserts an injective corona representation of `E/<w>` exists; this one is its negation, established through the audited block-amalgam structure and the involutive collapse.
  commuting-lamp-quotient-not-mf: That claim treats the Clifford witness modulo its sign, whose lamp kernel is elementary abelian; this one treats the literal presented group modulo its mark, whose lamp kernel is a free product of blocks, so the commuting-orbit hypothesis must be verified inside one block.
---

`E/<w>` is not MF: the image `ubar` of the unsquared defect
`u = [tct^{-1}, v_1]` is nontrivial in `E/<w>` and lies in
`Rad_MF(E/<w>)`.

**Consequences.**  Manuscript Question 1 ("Is `E/<w>` MF?") is resolved
negatively.  By the radical pullback (`cor:pullback`, formalized),

```text
Rad_MF(E) = q^{-1}(Rad_MF(E/<w>))  >  <w> :
```

the MF radical of the literal group is strictly larger than the marked
sign — `u` itself is the next visible element
(`unsquared-defect-mf-invisible`).  A sign-free finitely presented non-MF
group therefore exists inside the repository already: quotienting away the
Clifford-sign witness does not remove non-MF-ness, it reveals the
finite-orbit projection obstruction underneath
(`sign-free-compression-amalgam`).

**FORMALIZED 2026-08-16, with no block-amalgam input.**
`literal-mark-quotient-not-mf-parity-proof` replaces the route through
`literal-lamp-kernel-clifford-block-amalgam` by a translation-parity
argument that needs no normal form for the lamp kernel, so the claim now
rests on a zero-input Lean endpoint,
`LiteralSignFreeQuotient.signFreeQuotient_not_isCDEOperatorMF`.  Printed as
`thm:signfree` in `non_mf_groups_exist.tex`; manuscript Question 1 was
retired in the same pass.

**CLOSED STANDARD-MF ENDPOINT 2026-08-23.**  The Lean route now also proves,
without premises,

```text
LiteralSignFreeQuotient.signFreeQuotient_finitelyPresented
LiteralSignFreeQuotient.signFreeQuotient_not_isOperatorMF
LiteralSignFreeQuotient.exists_finitelyPresented_signFree_not_isOperatorMF
```

The finite-presentation proof identifies `⟨w⟩` internally with the normal
closure of the singleton `{w}`, so the quotient is obtained by adjoining one
relator to the literal finite presentation.  The standard operator-MF theorem
uses the proved equivalence with the genuine-corona convention.  The dedicated
`Endpoint/SignFreeCompressionAudit.lean` applies `#audit_closed_axioms` to the
finite-presentation theorem, the surviving unsquared defect, and the complete
existence endpoint.  This route does not invoke
`LiteralNonMFEndpoint.literal_not_isOperatorMF`: its detector is the
noncentral one-site involution and its witness is the unsquared two-lamp
commutator after the old central sign has been killed.

The public Lean reading path exports this route separately from the
central-sign route.  In particular, the theorem dependency closes through
`ProjectionCompressionCollapse.not_isCDEOperatorMF_of_involutiveWitness` and
the proved equivalence of the CDE and sequence-corona MF conventions; it does
not obtain non-MF by applying the old endpoint to the parent group.
