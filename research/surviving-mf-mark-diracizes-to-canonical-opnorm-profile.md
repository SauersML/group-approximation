---
rg: 2
id: surviving-mf-mark-diracizes-to-canonical-opnorm-profile
kind: claim
title: A surviving MF mark in a perfect central extension of a simple group yields an operator-norm model with regular packet profile
distinct_from:
  canonical-cross-gram-does-not-close-arbitrary-mf-active-profile: that firewall correctly shows that the ORIGINAL reblocked corona model keeps its arbitrary finite-packet multiplicity vector; this replaces the model by conjugate tensor powers and proves that a DIFFERENT surviving operator-norm model with the regular profile always exists, which is the intrinsic profile-forcing argument that firewall asks for.
  leavitt-regular-character-not-mf-without-property-t: that asks to exclude delta_e as an MF character of EL_n; this proves that a surviving mark forces operator-norm delta_e-microstates with the Plancherel packet profile, so any compiler contradicting those models proves that exclusion for the given rank.
  character-diracization-limit: that computes the pointwise limit of conjugate powers of one character in its GNS algebra; this realizes the limit by operator-norm asymptotic representations and identifies the scalar kernel inside the central subgroup.
  torsion-normal-generator-has-full-support-corona-core: that reblocks the original model to an active core of normalized rank at least 1/L with an arbitrary profile; this produces a model in which the marked involution has negative carrier of normalized rank tending to one half and every center-free finite packet has regular multiplicities.
artifacts:
  - research/surviving-mf-mark-canonical-opnorm-profile-proof.md
---

**ESTABLISHED (written proof; not Lean-verified).**  Let `Delta` be a
finitely generated perfect group, let `C<=Z(Delta)` be central, and suppose
`H=Delta/C` is simple.  Let `a in Delta` have finite order and nontrivial
image in `H`.  If

```text
Rad_MF(Delta) != Delta,
```

then there are a subgroup `K<=C` and operator-norm asymptotic unitary
representations

```text
W_j : Delta -> U(d_j)
```

with

```text
tr_(d_j) W_j(g) -> 1_K(g)          for every g in Delta.       (DCP1)
```

Consequently:

1. **Canonical trace.**  `tr W_j(g) -> 0` for every `g` outside `K`, hence
   for every `g` outside `C`.  When `C=1` (for example
   `Delta=EL_20(L_(F_2)(1,2))`), `W_j` is an operator-norm microstate of the
   canonical trace `delta_e`.
2. **Plancherel packet profile.**  For every finite subgroup `F<=Delta` with
   `F intersect K=1` (in particular every finite subgroup meeting `C`
   trivially), let `rho_j` be the same-dimension operator-norm
   exactification of `W_j|F`.  Then for every `lambda in Irr(F)`
   ```text
   tr rho_j(e_lambda) -> dim(lambda)^2/|F|.                    (DCP2)
   ```
   No finite packet can concentrate on a proper set of irreducible types.
3. **Full marked carrier without reblocking.**  If `a` is an involution,
   `||W_j(a)-1||_2 -> sqrt 2` and the `-1` spectral projection of the
   exactified `W_j(a)` has normalized trace tending to `1/2`.  More
   generally, if `<a> intersect K=1` and `a` has order `m`, every eigenvalue
   fraction tends to `1/m`.
4. **Survival.**  `W_j` defines a norm-matrix-corona homomorphism of `Delta`
   retaining `a` (indeed `||W_j(a)-1||_op>=sqrt 2-o(1)` for an involution).

Therefore any contradiction theorem which is valid for **every** surviving
operator-norm model may be applied to `W_j`.  Equivalently, to prove
`Rad_MF(Delta)=Delta` it suffices to contradict the existence of operator-norm
asymptotic representations with profile `(DCP1)` for some `K<=C`.  For
`EL_20(R)` this is exactly `K=1`.

## Scope

- The firewall
  `canonical-cross-gram-does-not-close-arbitrary-mf-active-profile` remains
  correct for the original model: tensor powers are a different model, and
  the typed native transports must be computed in `W_j`, not in the
  original `sigma_n`.
- The canonical profile is derived, not assumed.  The proof uses conjugate
  tensor powers, the Diracization limit, normal generation of `Delta` by the
  mark (perfectness plus simplicity of `H` plus centrality of `C`), and
  fixed finite-group operator-norm correction.  It uses no Property `(T)`,
  Kazhdan projection, spectral gap, or literature theorem.
- The models remain operator-norm models.  Nothing here is a
  normalized-Hilbert--Schmidt statement.  The HS-robustness fence
  `opnorm-native-cross-gram-does-not-promote-to-hyperlinearity` therefore
  still separates any conclusion drawn from `W_j` from the non-hyperlinear
  lane.
- For `St_20(R)` with `C=ker(St_20(R)->EL_20(R))`, the statement applies
  whenever that kernel is central.  It leaves a possible central phase
  subgroup `K`, and `(DCP2)` covers only packets meeting `K` trivially.

## What this removes and what it does not

Exact finite-packet countermodels whose multiplicity vector is not the
Plancherel vector do not obstruct a theorem quantified only over
`(DCP1)`-models.  This covers the one-irreducible concentration in the firewall
and the reducible or few-character profiles used in several fences recorded
under `binary-leavitt-arbitrary-profile-native-cross-gram`, for example the
two- and four-character source profiles and the zero-incidence reducible
packet.  Each such fence must be rechecked against the regular representation
of its packet before it is cited against the canonical quantifier.

It does **not** remove fences which are already realized by regular packet
models or by occurrence typing.  Examples are
`endpoint-whiteheads-are-center-chain-hecke-spectators`,
`fixed-center-chain-hecke-occurrence-is-regularly-impossible` and
`full-hecke-whitehead-zero-cross-gram`.

DERIVATION
surviving-mf-mark-canonical-opnorm-profile-proof
