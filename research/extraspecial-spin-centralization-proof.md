---
rg: 2
id: extraspecial-spin-centralization-proof
kind: route
title: Read the extraspecial commutator form before centralizing the clause
target: extraspecial-spin-predicate-centralization-kills-phase
requires: []
artifacts:
  - research/artifacts/elementary-group-closures-2026-08-30.md
---

Let `Z(E)=<J>` and let

```text
omega : E/<J> x E/<J> -> <J>,       omega(gbar,hbar)=[g,h]
```

be the commutator form.  For an extraspecial group this alternating form is
nondegenerate.  Hence, if `p` is noncentral, there is `x in E` with
`[p,x]!=1`; since the centre has order two, necessarily `[p,x]=J`.

Now put `E` in one player factor, commuting with the other player factor.  If
the normally imposed clause is `beta p b`, where `beta` is central and `b`
belongs to the other player factor, then its quotient satisfies

```text
1=[beta p b,x]=[p,x]=J.
```

Thus centralizing the noncentral player component kills the common phase.
The same calculation survives a private conjugator: for
`a=t^(-1)pt` and `y=t^(-1)xt`,

```text
[a,y]=t^(-1)[p,x]t=J
```

whenever `t` fixes `J`.  Consequently centralizing `a` also kills `J`.

Finally, this argument does not apply to the balanced word `[t,p]`.  Choosing
the above commutator witness as the image of `t` gives a homomorphism

```text
<E,t | [t,p]=J> -> E,       t |-> x,
```

which retains `J`.  This proves both the centralization firewall and its
claimed sharpness: private conjugacy cannot help, while balanced Britton
words require a genuinely global incompatibility argument.
