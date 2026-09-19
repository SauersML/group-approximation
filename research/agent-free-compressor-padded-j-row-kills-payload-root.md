---
rg: 2
id: agent-free-compressor-padded-j-row-kills-payload-root
kind: claim
title: One padded central-sign row kills the BCL payload root with bounded area
distinct_from:
  agent-free-compressor-full-corner-root-is-fd-invisible: That uses the packet Reynolds mismatch to kill the root only in exact finite-dimensional representations; this choice of quotient chart kills the coefficient and its root algebraically in the presented ring.
  agent-a4-bridge-transfers-forbidden-mass-but-stops-at-root-kill: That transfers forbidden mass to independent order-three letters while retaining them abstractly; this makes the BCL payload root trivial and therefore cannot be used in a literal cyclic amalgam.
  bcs-atom-detects-its-e5-central-root: That asks for a physical BCS atom to force spectral mass on a Steinberg root; this bounded root identity supplies no such physical-to-root implication.
---

Let `A<=B` be a finite packet inclusion whose common central involution is
`J`, and let `P` be a selected packet idempotent satisfying

```text
PJ=-P                                                     (PJR1)
```

over a finite splitting field `k` of odd characteristic `p`.  In the
construction of `finite-inclusion-is-free-self-compressor-quotient`, the
generator lists may be padded so that one basis generator `x_0` satisfies

```text
theta(x_0)=1,                 theta(alpha(x_0))=J.       (PJR2)
```

The endomorphism `alpha` remains injective and proper and still has
`theta(alpha(F))=A`.

For this choice, the coefficient rows `(BCL0)--(BCL2)` imply

```text
2P=0.                                                       (PJR3)
```

Consequently `P=0` in the presented coefficient ring.  In every rank at
least three its Steinberg root has a fixed bounded derivation

```text
x_ij(P)=1.                                                  (PJR4)
```

The same calculation is dimension-uniform in normalized Hilbert--Schmidt
norm: for an approximate unitary representation of any fixed finite
wordization of these rows,

```text
||rho(x_ij(P))-1||_2 <= C sqrt(E_pres),                     (PJR5)
```

where `C` depends only on the fixed presentation.

This does not solve the payload-localization problem.  It makes the root
trivial in the abstract group, whereas a physical forbidden projection in an
arbitrary unitary representation is not the spectral support of that root.
A representation may keep the finite BCS/packet factor and send every
Steinberg root to `1`.  Thus `(PJR5)` cannot be combined with forbidden BCS
mass without an additional theorem of the form
`bcs-atom-detects-its-e5-central-root`.

The distinction also protects perfect completeness.  In the preferred
perfect tracial BCS coefficient model the forbidden idempotent is already
`P=0`, so the padded conditional rows impose no new condition on the marked
central sign `J`.  But a **literal** amalgam identifying `x_ij(P)` with a
nontrivial finite bridge generator is then unavailable: `(PJR4)` makes that
cyclic map noninjective.  The padded row is therefore a bounded root-kill
device, not a payload-to-root bridge.

