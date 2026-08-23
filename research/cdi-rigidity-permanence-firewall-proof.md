---
rg: 2
id: cdi-rigidity-permanence-firewall-proof
kind: route
title: Pull back quotient characters and audit induction across finite index
target: standard-permanence-does-not-rigidify-the-cdi-image
requires:
  - ah-groups-fail-regular-fd-character-rigidity
  - cdi-character-cannot-be-promoted-by-regular-corners
  - cdi-character-rigid-image-quotient-is-an-exact-bridge
  - caprace-thom-v2-leaves-km-character-rigidity-open
  - simple-kazhdan-kac-moody-lattices-exist
---

If `q:G->K` is a proper quotient with `K` infinite ICC, then

```text
chi_q(g)=delta_e(q(g))                                  (CPF1)
```

is extremal, has GNS factor `L(K)`, and is nonregular on `G` because it is
one on `ker(q)`.  This proves the product/free-product/extension firewall
whenever the construction retains a proper infinite ICC quotient.  For a
tensor product representation the character is a pointwise product; on
`H x {e}` it remains `chi`, so multiplying by a regular character does not
make it `delta_(H x K)`.

The kernel statement follows from the last paragraph of
`cdi-character-rigid-image-bridge-proof`.  Group quotients are not functorial
quotients of a factor representation: a nonzero normal weakly closed ideal
of `Q` is all of `Q`.

For induction, finite index gives a finite matrix amplification whose
identity-coset corner contains the original GNS algebra.  This can preserve
non-CE, but it can import character rigidity only from a finite extension.
Acylindrical hyperbolicity is invariant under passage between finite-index
subgroups and overgroups, and
`ah-groups-fail-regular-fd-character-rigidity` then supplies `(CPF1)` inside
that overgroup.  At infinite index, the natural induced Hilbert space has
infinitely many equal coset fibers; the canonical matrix trace is
semifinite with infinite identity, not a tracial state.  Hence the induction
does not produce the finite factorial character required by the bridge.

Finally, simplicity of the Caprace--Remy group contradicts the proper
infinite quotient consequence of non-elementary acylindrical hyperbolicity,
and the current character theorem is absent by the cited Caprace--Thom
audit.  These facts prove the Kac--Moody assertions and complete the
permanence audit.
