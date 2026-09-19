---
rg: 2
id: locally-affine-support-bcs-is-exactly-the-lcs-boundary
kind: claim
title: Locally affine support is exactly the BCS-to-LCS boundary
root: true
artifacts:
  - research/locally-affine-support-bcs-is-exactly-the-lcs-boundary-proof.md
distinct_from:
  forbidden-character-kernel-quotient-compiler: that turns local kernel separation into a nonhyperlinear quotient; this identifies that local condition exactly with affine local support and with the existence of a non-CE LCS.
  perfect-completeness-constant-soundness-lcs-compiler: that asks for an effective machine-indexed compiler with quantitative soundness; this is a one-instance exact equivalence and uses no quantitative gap.
  centralized-clause-zero-face-is-exact-affine-bcs-quotient: that classifies assignment spectra after an exact clause quotient; this classifies which non-CE contextual traces can survive such a quotient and proves the converse construction.
---

The following are equivalent.

1. There is a finite Boolean constraint system `B`, a perfect tracial state
   `tau` on its synchronous algebra, and no Connes-embeddable perfect state,
   such that for every context `c`,

   ```text
   affineHull(supp(tau_c)) subseteq Allowed_c.          (LAS1)
   ```

2. There is a finite binary linear constraint system with a perfect tracial
   state and no Connes-embeddable perfect state.

3. There is a finitely presented nonhyperlinear group.

The equivalence of 2 and 3 is the solution-group equivalence recorded by
Paddock--Slofstra.  The new exact step is 1 if and only if 2.

For `1=>2`, replace every context predicate by the affine hull in `(LAS1)`.
Every finite affine subset of a Boolean cube is the solution set of finitely
many parity equations.  The state `tau` remains perfect because its local
support lies in that affine set.  Any Connes-embeddable perfect state for the
new LCS would also satisfy the original BCS, because the new affine allowed
set is contained in `Allowed_c` context by context.  This is impossible.

For `2=>1`, use the LCS itself as the BCS.  Each allowed set is affine, so
the affine hull of the local support of any perfect state remains inside the
allowed set.

In group terms, let `H_c` be the finite abelian context group and let
`S_c` be the character support of `tau|H_c`.  Put

```text
K_c=intersection_(chi in S_c) ker(chi).                (LAS2)
```

Then the character packet

```text
{chi: chi|K_c=1, chi(J)=-1}                            (LAS3)
```

is exactly `affineHull(S_c)`.  Quotienting by the finitely many generators
of the `K_c` imposes precisely the parity equations defining that affine
packet.  Thus the quotient in
`forbidden-character-kernel-quotient-compiler` is the solution group of the
locally extracted LCS.

This equivalence locates the endpoint sharply.  Local kernel separation is
not an extra analytic hypothesis: it is the exact algebraic content of an
LCS hidden inside the support of a non-CE contextual trace.
