---
rg: 2
id: predicate-activated-cnot-routes-relative-pauli-halves
kind: claim
title: A duplicated predicate commutator makes the relative-Pauli active/exit split an honest CNOT word
artifacts:
  - experiments/predicate_activated_cnot_router.py
distinct_from:
  relative-pauli-child-split-gives-one-exit-copy: that names two equal spectral halves but does not transport them to active and exit flags by group relations; this supplies the transport.
  child-carrier-relative-pauli-holonomy: that asks for the full three-context rank-one obstruction and HS payment; this is the finite one-edge router used inside each context.
---

Let `K` be any central involution word.  Form the finite class-two group

```text
H_K=<a,b,c,d,K |
     a^2=b^2=c^2=d^2=K^2=1,
     [a,b]=[c,d]=K,
     all cross commutators=1>.
```

The assignment

```text
phi(a)=ac,       phi(b)=b,
phi(c)=c,        phi(d)=bd                              (PCR1)
```

is an involutive automorphism of `H_K`.  Therefore the HNN extension adding
one stable letter `t` with `t x t^-1=phi(x)` for `x=a,b,c,d` is a fixed
ordinary group presentation and embeds `H_K`.  No relation `t^2=1` is needed.

On the sector `K=-1`, `(a,b)` and `(c,d)` are two commuting Pauli pairs.  On
the source flag `d=+1`, the two `b` spectral halves have equal trace, and
`(PCR1)` sends them to

```text
b=+1 -> target flag d=+1  (active),
b=-1 -> target flag d=-1  (exit).                      (PCR2)
```

On `K=+1` all four generators commute and `phi` merely permutes the abelian
characters.  Thus when `K` is the affine central commutator of a Schur rank
gate, the same four HNN relations route the active/exit halves exactly on the
violating sector while preserving every allowed selector sector.  There is no
controlled word, support deletion, or multiplicity-basis choice.

Completeness is explicit.  On an allowed `K=+1` sector choose the duplicated
pair trivially and map `t` to the identity.  On a violating `K=-1` packet,
tensor with one Pauli flag qubit and map `t` to the standard CNOT unitary.
Both choices satisfy the same presentation exactly.

The construction is local: it does not by itself make exit flags at different
clock levels first-hit orthogonal, nor does it identify the two child-active
flags with one returned Fanizza carrier.  It closes the finite group-word
realization of one relative Pauli split.
