---
rg: 2
id: random-coset-lamp-correlations-realize-every-irs-character
kind: claim
title: Random coset lamps realize every IRS character as an exact four-letter correlation
distinct_from:
  non-cohyperlinear-irs-exists: that says the IRS character is not a Connes-embeddable trace; this realizes its scalar values exactly but not as the trace of a group representation.
  non-ce-relation-admits-algebraic-action-envelope: that asks for a trace-preserving algebra embedding into one algebraic crossed product/group factor; this constructs only a measurable direct integral of subgroup-dependent wreath factors and identifies the missing multiplicativity.
  single-lamps-recover-set-action: that recovers a deterministic set action from its coordinate-lamp automorphisms; this computes canonical lamp moments for a random measurable family of coset actions.
  affine-haar-membership-does-not-promote-irs-trace: that gives a normal-subgroup counterexample to Haar-cylinder promotion; this supplies an exact generalized-lamp realization for an arbitrary IRS and proves directly why its moments still do not promote the trace.
---

Let `mu` be any IRS of a countable group `Gamma`, with character

```text
phi_mu(g)=mu({H:g in H}).                                (RCL1)
```

For each subgroup `H`, form the generalized wreath product

```text
W_H=(directSum_(Gamma/H) C_2) semidirect Gamma          (RCL2)
```

and let `a_H` be the involutory lamp at the base coset `H in Gamma/H`.
In the canonical trace of `L(W_H)`,

```text
tau_H(a_H g a_H g^(-1))=1_(g in H).                    (RCL3)
```

Indeed `g a_H g^(-1)=a_(gH)`.  If `gH=H`, the two lamps cancel and the
word is the identity; otherwise it is the nontrivial product of two distinct
lamp coordinates and has canonical trace zero.

The fields `H |-> L(W_H)`, `H |-> a_H`, and `H |-> g` are measurable: every
coefficient of every finite word is determined by finitely many subgroup-
membership cylinders.  Therefore the finite tracial direct integral

```text
M_mu=integral_(Sub(Gamma))^directSum L(W_H) dmu(H)      (RCL4)
```

contains the unitary field `A=(a_H)_H` and the representation
`U_g=(g)_H` of `Gamma`, with

```text
tau_(M_mu)(A U_g A U_g^*)=phi_mu(g).                   (RCL5)
```

Thus the generalized-lamp idea succeeds without approximation for every IRS,
including Manzoor's non-co-hyperlinear one.

It does **not** promote the IRS trace.  Fiberwise and hence in `(RCL4)`,

```text
tau_(M_mu)(U_g)=delta_(g,e),                            (RCL6)
```

the regular character, while the four-letter operators

```text
V_g=A U_g A U_g^*                                      (RCL7)
```

do not satisfy `V_g V_h=V_(gh)` in general.  Consequently `(RCL5)` gives
neither a trace-preserving homomorphism from the IRS GNS algebra nor an
embedding of that algebra into `M_mu`.  The non-CE character has been encoded
as a nonlinear correlation inside a measurable field, not as canonical
moments of a multiplicative group copy.

This pinpoints the exact promotion obligation.  To turn `(RCL5)` into a
group-factor construction one must either:

1. find multiplicative unitaries `T_g` in one group von Neumann algebra with
   `tau(T_g)=phi_mu(g)`, which is precisely a trace-preserving realization of
   the IRS GNS algebra; or
2. algebraize the measurable random coset-lamp bundle so that its relation
   algebra embeds into a compact-abelian Haar crossed product, which is the
   existing algebraic-envelope hole.

The lamp equality itself performs neither step.  It is nevertheless the
exact positive local formula any successful envelope must preserve.

