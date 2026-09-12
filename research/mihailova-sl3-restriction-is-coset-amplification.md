---
rg: 2
id: mihailova-sl3-restriction-is-coset-amplification
kind: claim
title: Restricting the Mihailova coset set to SL3 gives copies of one vertical-kernel coset action
distinct_from:
  mihailova-nonseparable-coset-stabilizer: that constructs the mixed stabilizer and records its vertical intersection; this computes the complete restricted SL3-set and dual module, including all orbit multiplicities.
  mixed-envelope-finitely-extracts-sl3-module-witness: that extracts some finite SL3-submodule from an arbitrary successful mixed module; this identifies every cyclic SL3-summand of the specific Mihailova permutation module.
  graph-coset-mixed-module-is-sofic: that proves soficity when the stabilizer projects injectively to the first actor factor; this stabilizer has the large vertical kernel computed here.
---

Let `Gamma` and `L` be countable groups, let `F<Gamma` and `E<L`, and let
`pi_1:F->Q` and `pi_2:E->Q` be epimorphisms.  Put

```text
P={(u,v) in F times E : pi_1(u)=pi_2(v)},
N=ker(pi_2),
Y=(Gamma times L)/P.                                  (MSR1)
```

Under the restricted left action of `{e} times L`, the map

```text
Y -> Gamma/F,                 (gamma,l)P |-> gamma F   (MSR2)
```

is the orbit map.  Every fiber is one transitive `L`-orbit, and each such
orbit is isomorphic to `L/N`.  Consequently, noncanonically as `L`-sets,

```text
Y = disjoint_union_(Gamma/F) L/N.                     (MSR3)
```

For the binary coset lamp module this gives

```text
direct_sum_Y C_2
  = direct_sum_(Gamma/F) direct_sum_(L/N) C_2          (MSR4)
```

as `F_2[L]`-modules, and dually

```text
C_2^Y = product_(Gamma/F) C_2^(L/N)                   (MSR5)
```

as compact Haar algebraic `L`-actions.

In the Mihailova candidate take `Gamma=Gamma_0`, `L=SL_3(Z)`, and the two
free subgroups mapping onto the Fournier--Facio `Q`.  The restricted
arithmetic action is therefore merely an amplification of the single
vertical-kernel coset action

```text
SL_3(Z) curvearrowright SL_3(Z)/ker(F_m->Q).           (MSR6)
```

The Manzoor/free coordinate contributes orbit multiplicity, not a new
`SL_3` stabilizer type.
