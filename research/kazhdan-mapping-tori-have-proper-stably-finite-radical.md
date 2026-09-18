---
rg: 2
id: kazhdan-mapping-tori-have-proper-stably-finite-radical
kind: claim
title: The mapping torus of a nontrivial MF Kazhdan group has a finite von Neumann representation that is nontrivial on the kernel, so no stably-finite certificate can prove the exact extrinsic radical
distinct_from:
  mf-kazhdan-quotientless-mapping-torus-exact-radical: That is the existence problem (XMF); this proves that every certificate for it which is valid in all stably finite targets fails, for every candidate pair (Q,psi).
  kazhdan-mf-hyperlinear-fragment: That gives a nontrivial tracial representation of the Kazhdan MF kernel alone; this extends one to the whole mapping torus, with a uniform Kazhdan lower bound that survives the automorphism.
  maximal-group-cstar-infinite-under-strict-compression: That shows strict Kazhdan compression makes the maximal group C*-algebra infinite; this shows such infiniteness never forces the Kazhdan kernel into the MF radical of a mapping torus.
  mf-hyperlinear-radical-divergence: That separates the MF and hyperlinear radicals at one mark of the literal group; this separates the MF radical from the stably-finite radical on the whole Kazhdan kernel of any candidate mapping torus in which (XMF) might hold.
  mapping-torus-mf-radical-descends-through-kernel-radical: That reduces the extrinsic branch (DX) to (XMF); this kills a whole class of approaches to (XMF).
---

**ESTABLISHED.**  For a group `G` let

```text
Rad_sf(G) = intersection of ker(sigma), over all homomorphisms
            sigma : G -> U(A), A a unital stably finite C*-algebra.
```

Let `Q` be a nontrivial group with property (T) that is MF, i.e. embeds in
`U(prod M_n / (+) M_n)`.  Let `(S,kappa)` be a Kazhdan pair for `Q` with `S`
finite.  Let `psi in Aut(Q)` and `G = Q semidirectProduct_psi Z`.
Then:

```text
(SF1)  Rad_sf(G) <= Rad_MF(G) <= Q x {0}, since the corona algebra is stably finite.
(SF2)  Some homomorphism sigma : G -> U(P), with P a finite von Neumann algebra
       with faithful normal tracial state, satisfies
         sum_{s in S} || sigma(s) - 1 ||_2^2  >=  kappa^2.
       So sigma is nontrivial on Q x {0}, and
         Rad_sf(G)  is a proper subgroup of  Q x {0}.
(SF3)  sigma is the tracial ultralimit of exact representations sigma_N of Q on
       M_N(M), with a unitary U_N (the cyclic shift) such that
         U_N sigma_N(q) U_N^* - sigma_N(psi(q))
       is supported on one diagonal block of normalized trace 1/N.
```

No soficity, finite presentation, torsion-freeness, quotientlessness or
outer order of `psi` is used.  Proof: `kazhdan-mapping-tori-have-proper-stably-finite-radical-proof`.

## What this kills

Suppose `(Q,psi)` is a candidate for
`mf-kazhdan-quotientless-mapping-torus-exact-radical`, where the goal is
`Rad_MF(G) = Q x {0}`.  Any argument for `q in Rad_MF(G)` that stays valid
for every unital stably finite C*-algebra target would put `q` in `Rad_sf(G)`.
By (SF2) such arguments cannot reach all of `Q`.  This kills:

- **Dedekind-finiteness certificates.**  Take a Kazhdan `L <= Q` and a
  compressor `t` of nonzero degree with `t L t^-1 <= L`.  In any finite target
  the Kazhdan projection satisfies `t p_L t^* >= p_L` with the two sides
  equivalent, so `t p_L t^* = p_L`.  Together with the relations of
  `C*_max(G)`, these forced equalities are true in `sigma`.  So they never
  kill `Q`, however they are combined.
- **Infiniteness of the maximal algebra.**
  `maximal-group-cstar-infinite-under-strict-compression` and Eckhardt's
  arXiv:2608.28772 Thm 3.1 say `C*_max(G)` is not finite.  That is compatible
  with a nontrivial stably finite quotient of `C*_max(G)` on which `Q` acts
  nontrivially.
- **Pimsner--Brown--Matui-type projection compression and ordered-K_0
  compression.**  These obstruct quasidiagonality of crossed products by
  forcing a positive class `psi_*(x) - x` to vanish.  Every such conclusion
  holds in any stably finite target, so it holds in `sigma`.
- **Tracial and invariant-measure obstructions** (Attempt 2 of (XMF)).  These
  are subsumed.
- **Certificates that use norm models of `Q` only.**  The input `tau` below
  is itself the tracial ultralimit of the norm moving corner of `Q`, from
  `kazhdan-mf-hyperlinear-fragment`.  So a certificate that uses norm accuracy
  for the relations of `Q`, but only trace-accuracy for the stable letter,
  dies too.

**Invariant.**  The normalized trace of the set on which the relations
`t q t^-1 = psi(q)` fail.

**Step where every member dies.**  Evaluation at `sigma_N`.  The conflict is
parked on one wrap block of trace `1/N`, while the Kazhdan lower bound is spread
evenly over all `N` blocks.

**What survives.**  A proof of (XMF) must use operator-norm
almost-multiplicativity of the stable-letter relations on a block of vanishing
normalized trace.  This is exactly the wrap block of weight `1` found in
Attempt 1 of (XMF).  The normal-Kazhdan defect engine
(`normal-kazhdan-defect-non-mf`) survives: its HS-triviality of defects is
extracted from norm models of the whole group, compressor included.  So the
recipes of Attempts 3--5 are not affected.  Periodization proofs of MF-ness
(Attempt 1) and these certificates for non-MF-ness fail at the same block.

**Consequence for the flagship.**  In branch (DX) of
`mapping-torus-mf-radical-descends-through-kernel-radical`, the MF quotient
`Q = K/Rad_MF(K)` need not be hyperlinear.  Even so, no stably-finite
certificate can give `Rad_MF(Q semidirectProduct_psi Z) = Q`.  In every
branch, a witness `G` is sofic, hence hyperlinear, so `Rad_sf(G) = 1`.
