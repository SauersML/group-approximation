---
rg: 2
id: dummy-abelianized-cover-df-splits-regular-trace-and-shadow
kind: claim
title: For the dummy abelianized cover, non-MF splits into a regular-trace obstruction and a shadow-to-MF transfer
distinct_from:
  character-diracization-limit: that computes the pointwise limit of conjugate powers of one character; this uses it inside the closed convex semigroup of operator-norm MF characters and uses the self-centralizing kernel to force the scalar kernel to be trivial, so the limit is the regular character of the cover itself.
  surviving-mf-mark-diracizes-to-canonical-opnorm-profile: that needs a perfect central extension of a simple group and a finite-order mark; this is for the torsion-free abelian-by-G cover, has no mark and no simplicity, and replaces "central kernel" by "self-centralizing kernel".
  abelianized-cover-injective-corona-model-carries-nonzero-twist: that constrains the twist of an injective model; this says which trace an injective model can be assumed to carry, namely delta_e, exactly when the shadow residual is trivial.
  op-to-hs-shadow-residual-functoriality: that defines the shadow residual S(G) and proves its functoriality; this proves that for the dummy cover S(E_z)=1 is equivalent to operator-norm microstates of delta_e and is decided on the relation module.
  mf-vs-tracial-radical-strict-gap: that separates Rad_MF from S on a lamp wreath with a Kazhdan compression; this isolates the implication S != 1 => Rad_MF != 1 as one of the two prerequisites of DF for the dummy cover, and that gap example shows it is not a formal principle for abelian-by-G extensions.
  full-mf-radical-abelianized-cover-is-not-mf: that is the target (DF) for every presentation; this proves an equivalence for the dummy presentation, whose cover retracts onto the original cover, so DF for any presentation implies DF for its dummy presentation.
artifacts:
  - research/dummy-abelianized-cover-df-split-proof.md
  - research/abelianized-cover-kernel-is-self-centralizing.md
  - research/character-diracization-limit.md
---

**ESTABLISHED (written proof; not Lean-verified).**

## Setting

Let `G=F(X)/R` be countable and finitely generated.  Adjoin a dummy generator
`z` with `q(z)=1`, and set

```text
F_z = F(X u {z}),   R_z = ker(F_z -> G),   E_z = F_z/[R_z,R_z],   M_z = R_z/[R_z,R_z].
```

An **operator-norm MF character** of a countable group `Gamma` is a function
`tau` on `Gamma` such that, for every finite `S` in `Gamma` and every
`delta>0`, some map `phi:Gamma->U(d)` satisfies

```text
||phi(ab)-phi(a)phi(b)||_op <= delta  and  |tr_d phi(g) - tau(g)| <= delta     (a,b,g in S).
```

Write `T_op(Gamma)` for the set of these.  Every limit trace of every
norm-matrix-corona homomorphism lies in `T_op(Gamma)`.  The **shadow residual**
is

```text
S(Gamma) = { g : tau(g)=1 for every tau in T_op(Gamma) } = R_(infinity->2)(Gamma),
```

and `Rad_MF(Gamma) <= S(Gamma)`.

## Statement

1. **Every nontrivial normal subgroup of `E_z` meets `M_z`.**  In particular
   ```text
   Rad_MF(E_z) != 1  iff  Rad_MF(E_z) cap M_z != 0,
   S(E_z) != 1       iff  S(E_z) cap M_z != 0.
   ```
2. **Regular-trace criterion.**  The following are equivalent:
   - (a) `delta_e in T_op(E_z)`, i.e. the canonical trace of `E_z` has
     operator-norm microstates;
   - (b) `S(E_z)=1`;
   - (c) every nonzero `m in M_z` has some `tau in T_op(E_z)` with `tau(m)!=1`;
   - (d) some single `tau in T_op(E_z)` has `|tau(m)|<1` for all
     `m in M_z \ {0}`.

   When they hold, `E_z` is MF, by a corona homomorphism `W` whose limit
   trace is `delta_e`.
3. **Structure of a regular model.**  In such a `W`,
   `C*(W(M_z)) ~= C(hat M_z)` has full spectrum and trace equal to Haar
   measure.  `G` acts on it by the dual of the module action.  This action
   fixes the trivial character, is essentially free, and is mixing, because
   nonzero elements of `M_z <= Z[G]^n` have finite stabilizers.
4. **Decomposition of DF.**  For the dummy cover,
   ```text
   Rad_MF(E_z) != 1   <=>   (REG) and (SH),
   (REG)  delta_e is not an operator-norm MF character of E_z
          (equivalently: some nonzero m in M_z is Hilbert--Schmidt-killed by
          every operator-norm asymptotic representation of E_z);
   (SH)   S(E_z) != 1  implies  Rad_MF(E_z) != 1.
   ```
   `(REG)` is a canonical-trace statement: by item 3, it only has to
   contradict models with the Haar profile on the whole dual `hat M_z`,
   including the `G`-fixed point.  `(SH)` is a shadow-to-MF transfer, and it
   is the only place where tracially blind models, such as `rho (+) 1_(N_n)`,
   have to be handled.

## Scope

- The two prerequisites can fail independently.  If `(REG)` fails, `E_z` is
  MF, which refutes DF for this presentation.  If `(SH)` fails, some
  tracially blind injective model exists while every model is HS-blind on a
  nonzero submodule of `M_z`.
- `mf-vs-tracial-radical-strict-gap` shows that `(SH)` is not a formal
  principle for abelian-by-`G` extensions.  Its lamp wreath
  `Z^(H/tLt^-1) x| H` has a lamp-module commutator in `S` but not in
  `Rad_MF`, and that example uses a Kazhdan compression.  So any proof of
  `(SH)` for `E_z` needs group input.
- The route `property-t-free-seed-via-leavitt-abelianized-cover` needs DF for
  one presentation.  `E_z` retracts onto `E=F/[R,R]` (kill `z`; include
  `F(X)`), so DF for `E` implies DF for `E_z`.  Both covers are torsion-free
  and finitely generated, so either one feeds the torsion-free embedding
  step.  This claim does not prove DF for the original presentation from DF
  for `E_z`.
- No Property (T), spectral gap, or reblocking is used.

DERIVATION
dummy-abelianized-cover-df-split-proof
