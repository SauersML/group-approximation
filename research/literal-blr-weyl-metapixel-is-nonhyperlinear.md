---
rg: 2
id: literal-blr-weyl-metapixel-is-nonhyperlinear
kind: claim
title: A literal BLR--Weyl metapixel is already a nonhyperlinear group
distinct_from:
  finitely-presented-uniform-area-clifford-tape: that asks for a uniformly bounded multiplication table as input; this proves that globally named BLR and twisted-commutation prototypes automatically produce that table.
  finite-orbit-occurrence-pauli-compiler: that permits contextual occurrence names and still needs a consistency decoder; this theorem assumes one global word for each BLR question and pinpoints why contextual orbit representatives do not suffice.
---

Let `Gamma=<S|R>` be finitely presented and let `j` be a word.  Suppose that
for every `N` there are words

```text
x_N(a), z_N(phi),       a in F_2^N, phi in (F_2^N)^*,          (LBW1)
```

and one constant `L`, independent of `N`, such that the following words have
`R`-area at most `L`:

```text
j^2,
x_N(a)x_N(b)x_N(a+b)^-1,
z_N(phi)z_N(psi)z_N(phi+psi)^-1,
[x_N(a),z_N(phi)]j^-phi(a).                                  (LBW2)
```

If `j!=1` in `Gamma`, then `Gamma` is nonhyperlinear.

In particular, it is enough that all the relations in `(LBW2)` are literal
conjugates of finitely many prototype relators: adjoining those finitely many
prototypes to the presentation gives `L=1`.  Thus no amenable or sofic group
can be such a host with a nontrivial mark.  This excludes metabelian groups
and finitely generated linear affine groups in particular.

The obstruction is not orbit enumeration.  Under the simultaneous linear and
contragredient actions, BLR pairs `(a,b)` and Weyl pairs `(a,phi)` each have
only five orbit types.  What fails in the amenable oligomorphic and
linear-affine models, and what remains precisely unproved for the Thompson
tape, is the passage from a contextual simultaneous transporter to the fixed
global words in `(LBW1)` with bounded area.  If that passage had
dimension-independent normalized-HS cost, `(LBW2)` would give a uniformly
bounded complete Pauli table and hence the stated contradiction.

This is precisely the binary-answer BLR/Weyl core of the Natarajan--Vidick
many-qubit Pauli test.  The obstruction therefore does not come from its
answer alphabet; it comes from demanding globally named word representatives
and literal prototype cost simultaneously.
