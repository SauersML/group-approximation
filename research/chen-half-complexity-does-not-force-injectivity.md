---
rg: 2
id: chen-half-complexity-does-not-force-injectivity
kind: claim
title: Chen's universal one-half complexity bound does not force coefficient injectivity
invalidates: [simple-kl-via-chen-half-complexity]
artifacts:
  - research/artifacts/kl-cyclic-orbit-audit-2026-08-24.md
---

Write

    N_m = A * <z>,       A = *_{i=0}^{m-1} S_i.

Every cyclic-orbit relator `w_i` in `kl-cyclic-orbit-perfect-kernel` is
unimodular with respect to `z`, because `deg_t(w_i)/m=1`.  Chen's Corollary
6.5 applies to an arbitrary free factor `A` and gives, for every
boundary-incompressible `w_i`-admissible surface `Sigma`, only

    -chi(Sigma) >= (1/2) deg(Sigma)

without a torsion hypothesis.

For a minimal collapse identity using `k` conjugates of one unimodular
relator, the associated punctured sphere has

    -chi(Sigma)=k-1,       deg(Sigma)=k.

The universal estimate therefore says only `k-1>=k/2`, compatible with every
`k>=2`.  It cannot supply the standard contradiction.  The coefficient-one
estimate would give `k-1>=k`, but Chen obtains coefficient one from the
torsion-free case or, in the HNN-local formulation, from the relevant
`infinity`-RF and `infinity`-RTF turn-label hypotheses.

For a trivial edge subgroup, Chen's Definition 5.1 says that
`infinity`-RF is exactly infinite order (equivalently, the generated subgroup
is `Z`).  Thus an HNN enlargement does not hide torsion: it merely relocates
the missing infinite-order hypothesis.  Theorem 5.3 and Corollary 5.4 do give
injectivity when the stronger relative-freeness hypotheses hold, but those
hypotheses are not automatic for the arbitrary simple groups in the Cairn
reduction.

This numerical observation concerns the bare one-relator estimate.  The
canonical `Q_w` has `m` orbit relators, so the observation is not being used
as a multi-relator theorem and does not assert that Chen's machinery can
decide `Q_w!=1`.
