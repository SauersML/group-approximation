---
rg: 2
id: genuine-hnn-switches-over-amenable-bases-are-sigma1
kind: claim
title: Genuine finite HNN switches over amenable bases have only a Sigma-zero-one amenable locus
distinct_from:
  finitely-generated-centralizer-switches-are-sigma1: that treats the special centralizing HNN extension; this treats every genuine one-edge HNN extension with finitely generated associated subgroups and also closes the noninjective endomorphism loophole.
  lamplighter-fp-amenable-interface-is-directional: that supplies one amenable finite-presentation overgroup of the lamplighter; this proves why a uniform switch cannot be obtained by varying a genuine finite HNN edge over an amenable base.
  amenability-of-finite-presentations-is-pi2-complete: that is the open completeness root; this is a no-go theorem for a broad proposed compiler class.
---

**ESTABLISHED.**  Let `e |-> B_e=<X_e|R_e>` be a computable family of
finite presentations, all presenting amenable groups.  Let finite word
tuples `h_e=(h_(e,1),...,h_(e,r))` and
`k_e=(k_(e,1),...,k_(e,r))` generate subgroups `H_e,K_e<=B_e`, and
assume as part of the uniform construction that
`h_(e,i)|->k_(e,i)` induces an isomorphism
`theta_e:H_e->K_e`.  Put

```text
P_e=<B_e,t | t^-1 h_(e,i) t=k_(e,i), 1<=i<=r>.          (GHS1)
```

Then

```text
P_e is amenable  iff  H_e=B_e or K_e=B_e.               (GHS2)
```

Either equality makes `(GHS1)` an ascending HNN extension of the amenable
base and hence amenable.  If both associated subgroups are proper,
Bass--Serre tree ping-pong gives a nonabelian free subgroup.

Each equality in `(GHS2)` is `Sigma^0_1`, uniformly in `e`: for every
presentation generator of `B_e`, guess a word in the displayed generators
of `H_e` or `K_e` and finite van Kampen derivations of the resulting
finite packet of equalities.  Hence

```text
{e:P_e is amenable} is Sigma^0_1.                        (GHS3)
```

No such genuine finite-edge HNN family can many-one encode `TOT` or prove
[[amenability-of-finite-presentations-is-pi2-complete]].

Dropping injectivity does not provide an endomorphism mapping-torus loophole.
For every amenable group `B` and endomorphism `phi:B->B`,

```text
M(B,phi)=<B,t | t^-1 b t=phi(b), b in B>                (GHS4)
```

is amenable.  Its base image is
`B/K_infty`, where `K_infty=union_n ker(phi^n)`; `phi` induces an
injective endomorphism there, and `(GHS4)` is the corresponding ascending
HNN extension, equivalently an amenable direct limit extended by `Z`.

Thus an amenable finitely presented solvable simulator stays amenable under
every endomorphism mapping-torus and cannot supply the negative branch.  A
successful totality compiler must control a non-genuine stable kernel, not a
genuine finite edge over an amenable base.

DERIVATION
[[genuine-hnn-switches-over-amenable-bases-sigma1-proof]]
