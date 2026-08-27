---
rg: 2
id: selberg-regular-orbit-retraction-proof
kind: route
title: Average the identity, polar-complete, and use equality of characters
target: regular-congruence-endpoint-orbit-has-uniform-selberg-retraction
requires:
  - odd-congruence-iwahori-pairs-have-uniform-linear-repair
---

On normalized Hilbert--Schmidt matrices use the left-right representation

```text
beta(g)A=rho(g)A eta(g)^*.
```

The uniform Selberg constant `kappa` from
`odd-congruence-iwahori-pairs-have-uniform-linear-repair` applies to this
odd-congruence representation.  If `E` is conditional expectation onto
`Fix(beta)` and `A=E(I)`, then

```text
||A-I||_2<=epsilon/kappa=:delta.                       (SRP1)
```

Write `A=U|A|`.  Its initial and final supports `p=U^*U`, `q=UU^*` reduce
`eta(Q)` and `rho(Q)`, and `U` intertwines the two restricted
representations.  As in the odd-congruence repair proof,

```text
tr(1-p)=tr(1-q)<=delta^2,
||(U-I)p||_2<=2delta.                                  (SRP2)
```

Here equality of the **total characters** supplies the improvement over
trivial-complement repair.  The subrepresentations on `p` and `q` are
equivalent through `U`; subtracting their common character from
`chi_eta=chi_rho` shows that the complementary representations on `1-p`
and `1-q` are equivalent as well.  Choose an exact complementary
intertwiner `W:(1-p)H -> (1-q)H` and set `V=U+W`.  Then `V` is a unitary
intertwining all of `Q`, and the complement has normalized rank at most
`delta^2`.  Therefore

```text
||V-I||_2<=4delta,                                     (SRP3)
```

with the same polar/Mirsky estimate as in the cited proof.  This proves
`(SOR2)`.  Since `eta(g)=V^*rho(g)V`, two-term telescoping proves `(SOR3)`.

Since `rho(w)` is the identity-gauge member of `O`, `(SOR3)` first gives
the orbit-distance estimate `(SOR4)`.  If the two representations agree
on `K`, the intertwining identity gives
`V rho(k)=rho(k)V` for every `k in K`.  Hence `V in rho(K)'`, and evaluation
at `w` gives the exact orbit identity `(SOR5)`.
