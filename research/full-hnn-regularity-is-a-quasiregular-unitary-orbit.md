---
rg: 2
id: full-hnn-regularity-is-a-quasiregular-unitary-orbit
kind: claim
title: Full HNN regularity makes the stable-letter orbit an exact quasiregular unitary frame
distinct_from:
  sl3-regular-double-bass-serre-rigidity-firewall: that exhibits one block-swap vector in the exact amalgamated free product factor; this computes the entire stable-letter conjugacy Gram matrix forced in any full canonical HNN matrix ultraproduct.
  no-exact-quasi-regular-leak: that asserts no such unitary frame can occur in a matrix ultraproduct; this is the unconditional normal-form calculation of the payload supplied by full HNN regularity.
  canonical-trace-does-not-weaken-thin-commutant-transfer: that regularizes only the actor character by a tensor factor carrying trivial stable letter; this records precisely the mixed stable-letter moments which that camouflage cannot create.
---

Let

```text
C=SL_3(Z),       A=SL_3(Z[1/2]),
G=<A,t | [t,C]=1>.
```

Suppose a full canonical-character microstate sequence for `G` defines in a
tracial matrix ultraproduct a homomorphism `pi:G->U(M)`.  Put `k=pi(t)` and

```text
k_(aC)=pi(a)kpi(a)^*.                                  (HQR1)
```

Then `(HQR1)` is well defined and is an exact orthonormal unitary frame
indexed by `A/C`:

```text
tau(k_(aC)^* k_(bC))=1_(aC=bC).                       (HQR2)
```

The actor acts by the quasiregular permutation of this frame.  Equivalently,

```text
k in pi(C)',
tau(k^*pi(g)kpi(g)^*)=1_C(g)             (g in A).    (HQR3)
```

For `h=diag(2,1,1/2) notin C`, `(HQR3)` forces

```text
1-|tau([k,pi(h)])|^2=1,                                (HQR4)
```

while every source `C`-energy is zero.  Thus full HNN regularity does not
make projective transfer quantitatively easier: it fixes the desired
inequality's two sides at the maximally contradictory values `1` and `0`.
A transfer theorem on this branch is exactly a theorem that no such matrix
microstates exist.

This is the genuine payload absent from actor-only tensor camouflage.  It
is stronger than regularity of `pi|A`: all nontrivial reduced words in the
conjugates `{k_(aC)}` also have trace zero.  But the same configuration
exists exactly in `L(G)`.  Consequently its refutation must use matrix
ultraproduct embeddability, not trace positivity, the regular character, or
Bass--Serre identities alone.

