---
rg: 2
id: kl-test-word-conjunction-fence
kind: claim
title: Coefficient-free test words cannot conjoin the two incompatible KL transports
artifacts:
  - research/kl-test-word-conjunction-fence-proof.md
distinct_from:
  leavitt-corners-cannot-compress-external-variable: that rules out additive Leavitt corner packing; this rules out the natural purely group-theoretic test-word replacement.
  leavitt-omega-has-an-explicit-distorted-target: that supplies the incompatible source and target pairs; this proves that applying one common test word to those pairs does not transport either component.
  kl-violating-equation-over-leavitt-unit-group: that requires one nonsingular relative relator killing a coefficient; this is a no-go theorem for two tempting compiler classes and supplies no such relator.
---

Let

```text
E_a(t)=t^(-1)atc^(-1),       E_r(t)=t^(-1)rtp^(-1)
```

be the two incompatible Leavitt transports.  They cannot have a
**nonsingular consequence**: their normal closure is contained in the kernel
of the stable-letter degree map.  In particular, no nonsingular equation is
equivalent to, or justified as a one-word compression of, this two-equation
system.  A viable KL word must be strictly stronger and self-referential.

The standard group-theoretic test-word attempt also fails.  For every
coefficient-free two-variable word `V`,

```text
V(t^(-1)at,t^(-1)rt)=V(c,p)
```

is merely the cyclic transport

```text
t^(-1)V(a,r)t=V(c,p).
```

Whenever the two displayed cyclic subgroups are isomorphic under the indicated
map, Britton's lemma embeds the whole coefficient group in the resulting HNN
extension.  Thus even a free-group `C`-test word transports only its value,
not the two entries, in the arbitrary overgroups quantified over by KL.

Finally, there is no coefficient-free word `W(X,Y)` whose identity fiber is
`{(1,1)}` in every group.  In a sufficiently large cyclic group its value is
one linear equation in two variables and has a nonzero solution.  Therefore a
universal commutator/product detector cannot repair the test-word construction;
successful packing must use the special coefficient geometry inside the
relative normal closure.
