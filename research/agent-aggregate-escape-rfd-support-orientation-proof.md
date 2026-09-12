---
rg: 2
id: agent-aggregate-escape-rfd-support-orientation-proof
kind: route
title: Test the exact support row against finite-dimensional separation and extension
target: agent-aggregate-escape-rfd-support-orientation-firewall
requires:
  - agent-aggregate-escape-central-support-orientation-terminal
  - role-packed-bcs-gap-is-one-idempotent
  - index-two-reynolds-hnn-is-a-proper-corner-section
  - packet-kazhdan-commutant-placement-decouples
  - kazhdan-and-transverse-packets-cannot-orient-clifford-twist
  - explicit-finite-face-ucp-section-is-edge-equivariant
  - kernel-relator-forces-two-edge-ucp-section-gap
  - virtually-free-full-algebras-are-rfd
---

Set `E=0` in `(ACO4)`.  Every summand is nonnegative, so

```text
0=sum_i ||pi(T e_i)||_2^2
```

implies `pi(T e_i)=0` termwise.  Intersecting over all finite-dimensional
unitary representations proves `(RF1)--(RF2)`.

If `C*(Gamma)` is RFD and `T e_i!=0`, some finite-dimensional
representation detects it, contradicting `(RF1)`.  If `Gamma` is residually
finite, write the nonzero group-algebra element as

```text
T e_i=sum_(g in S) c_g g
```

with finite support `S` and distinct group elements.  Residual finiteness,
applied to the finite set `{g^(-1)h:g,h in S,g!=h}`, supplies a finite
quotient injective on `S`.  The quotient group-algebra image remains
nonzero, and its finite-dimensional left regular representation detects it.

For `(RF3)`, `e_i` is a nonzero projection in `C[F_i]` and `T` is the
nonzero negative character projection of the independent central `C_2`.
Their tensor product `T e_i` is nonzero in
`C[F_i direct_product C_2]`.  Full group C-star algebras preserve subgroup
inclusions (induce any subgroup representation to the ambient group), so it
remains nonzero in `C*(Gamma)`.

If a finite quotient is injective on this subgroup, its regular
representation restricts to `[Q:<F_i,K>]` copies of the subgroup regular
representation.  Normalization cancels this multiplicity.  The product
trace factors across `F_i direct_product <K>`, giving
`tau(T e_i)=tau(T)tau(e_i)=tau(e_i)/2`, which proves `(RF3')` and the stated
role-packed value.

The local Reynolds/Schur construction has a finite base and only
finite-subgroup Bass--Serre edges before the unresolved global placement.
Such a finite graph of finite groups is virtually free and residually
finite, while its vertex groups embed.  The preceding argument therefore
gives an exact finite-dimensional countermodel to `(ACO4)` for the local
cell.

More generally, if a marked finite-dimensional local representation extends
after amplification to an attachment, its extended representation still
has `pi(T e_i)!=0`; normalized amplification preserves the squared HS mass.
This proves the marked-extension-functorial firewall and applies to the
recorded actor spectator models.

Finally, `(KUG1)` is an operator-norm lower bound on one lift discrepancy.
This obstruction has an explicit HS dilution.  The virtually free group `E`
is RFD, so a finite-dimensional representation `pi_bad` detects the norm gap
to arbitrary accuracy.  On the other hand, for every representation `sigma`
of the finite quotient `P_13`,

```text
pi_good=sigma o q
```

annihilates every lift discrepancy because `q_* o T=id`.  In
`pi_bad direct_sum N pi_good` the operator norm gap persists, while its
normalized squared HS contribution is at most a fixed constant times
`dim(pi_bad)/(dim(pi_bad)+N dim(pi_good))`, which tends to zero.  Thus no
normalized-HS density estimate such as `(RF4)` follows without a separate
positive-density identification with `T e_i`.
