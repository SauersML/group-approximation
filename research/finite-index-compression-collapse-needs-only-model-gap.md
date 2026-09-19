---
rg: 2
id: finite-index-compression-collapse-needs-only-model-gap
kind: claim
title: At finite compression index the torsion compression collapse needs no FH step and no Kazhdan finite generation, only the Kesten model spectral gap of one corona model
distinct_from:
  kazhdan-coboundary-collapse: that is the Delorme-Guichardet coboundary step of the collapse, which uses FH of Lambda; this shows that when [Lambda:s Lambda s^-1] is finite the cocycle is constant on cosets of the compressed copy, so an explicit coset average is an H-fixed primitive and FH is never invoked.
  kesten-spectral-gap-replaces-kazhdan-projection-per-model: that replaces (T) by (MSG) in thm:transport and thm:normal-kazhdan of the manuscript (central-sign route), where no cocycle occurs; this does the same for the lamp/torsion compression collapse of notes/COMPRESSION_COLLAPSE_MF_RADICAL.md, whose proof also consumes FH and Kazhdan finite generation, and shows that at finite index those two inputs disappear.
  compression-torsion-collapse: that is the collapse with Lambda Kazhdan; this is the finite-index collapse with (T) replaced by one per-model spectral hypothesis.
  universal-fixed-projection-forces-kazhdan-subgroup: that proves a universal fixed projection forces (T); this uses only the fixed projection of one model, so it is not a universal statement and is consistent with that obstruction.
  model-spectral-gap-quantifier-ladder: that shows representation-generic proofs of (MSG) are Kazhdan theorems; this shows that at finite index (MSG) is the only analytic input left, so that ladder now governs the lamp collapse as well as the central-sign transport.
artifacts:
  - research/finite-index-compression-collapse-needs-only-model-gap-proof.md
  - notes/COMPRESSION_COLLAPSE_MF_RADICAL.md
  - research/kesten-spectral-gap-replaces-kazhdan-projection-per-model.md
---

**ESTABLISHED (written proof; not Lean-verified).**  Decomposition /
belief correction.

**Setting.**  That of Theorem 1 of `notes/COMPRESSION_COLLAPSE_MF_RADICAL.md`
with property (T) of `Lambda` deleted: `W` countable, `pi: W -> U(Q_d)` a
norm-corona homomorphism with lifts `U_{g,n}`, `s in W` with
`H = s Lambda s^-1 <= Lambda`, and `k in W` with `pi(k)^m = 1`, pairwise
commuting `Lambda`-orbit images, and `pi(hkh^-1) = pi(k)` for `h in H`.
Let `B = prod_n B(M_{d_n}, ||.||_2) / direct_sum` be the adjoint corona and
`sigma~ = [Ad U_{g,n}] : W -> U(B)`.

**Theorem.**  Assume

- (F) `Lambda` is finitely generated, with finite symmetric generating
  set `S` containing `e`;
- (I) the compression index `[Lambda : H]` is finite;
- (MSG) `1` is not an accumulation point of `sp_B(sigma~(h_S))`,
  `h_S = |S|^-1 sum_{a in S} a`;
- (L) exact commuting `m`-torsion lifts exist (Step 1 of the note; for
  `m = 2` this is the Lean theorem
  `ExactInvolutionLifts.exists_isExactInvolution_comm_of_unitary`).

Then `pi(lambda k lambda^-1) = pi(k)` for every `lambda in Lambda`.

**What changed.**  Section 2 of the note says (T) is used three times:
finite generation (Step 3), FH (Step 5) and the spectral gap in transport
(Step 6), and "none of the three is removable".  At finite index this is
false for the first two:

1. Step 3 needs only (F).
2. Step 5 needs nothing.  The rank cocycle `c` on the rescaled
   ultraproduct `K_omega` vanishes exactly on `H`, so `c(lambda h) = c(lambda)`.
   It therefore takes at most `[Lambda:H]` values and is bounded, and
   `w = -[Lambda:H]^-1 sum_{lambda H} c(lambda)` is an `H`-fixed
   primitive.  This is the elementary coset average, not Delorme--Guichardet.
3. Step 6 needs only (MSG) in the one model.  The eigenprojection
   `P = chi_{1}(sigma~(h_S))` lies in the finite C-star algebra `B`, and
   `sigma~(s) P sigma~(s)* >= P`.  So finiteness of `B` (a rank count on
   lifts) forces equality, which is exactly the transport of `H`-fixed
   vectors to `Lambda`-fixed vectors on `K_omega`.

So the whole (T) content of the finite-index lamp collapse is one
isolated eigenvalue of one Markov element in one adjoint corona.

**Scope.**  Finite index covers the manuscript's own seed, the index-8
compression `(v,A) -> (2v,A)` of `Z^3 x| SL_3(Z)`.  It also covers every
instance of `sign-free-compression-amalgam` (index `m`), and the
permutational lamp groups `K^(Lambda/H) x| Lambda` over ascending HNN
extensions along finite-index self-embeddings.

**Consequence for the goal.**  For these witnesses a (T)-free non-MF
proof is now exactly a (T)-free proof of (MSG) on `Lambda` along every
corona model of `W`.  By `model-spectral-gap-quantifier-ladder` this must
use matrix-origin information: a proof that works for every
representation is a Kazhdan theorem.  Cohomological substitutes for (T)
are irrelevant at finite index, because FH was never needed there.
These include relative FH, vanishing of `H^1` of the rescaled
representation, and bounded generation of cocycles.  Any approach that
spends effort on the FH side of the lamp collapse at finite index dies
at this theorem.

**Not claimed.**  Nothing is said for infinite-index compressions, where
`c|_H = 0` does not bound `c` and a spectral gap does not kill `H^1`.
The theorem gives no (T)-free proof of (MSG), and the goal stays OPEN.

Proof: `finite-index-compression-collapse-needs-only-model-gap-proof`.
