---
rg: 2
id: degree-zero-leavitt-core-characters-are-dirac-haar-mixtures
kind: claim
title: Every character of the degree-zero Leavitt core is a mixture of the trivial and the regular character, so every MF character of the Leavitt group is Dirac--Haar on the core
artifacts:
  - research/degree-zero-core-dirac-haar-proof.md
  - research/artifacts/leavitt-character-transfer-audit-2026-09-05.md
distinct_from:
  binary-leavitt-steinberg-mf-characters-are-trivial: that is the open target asserting every MF character of the Steinberg group is trivial; this is an established classification of ALL characters on the degree-zero core, which reduces that target to excluding a regular component and shows the Haar row profile is the only possible nontrivial restriction.
  surviving-leavitt-corona-character-has-infinite-parabolic-orbit: that excludes finite nonzero parabolic orbits for the row-module spectral measure; this computes the restriction of every character to every degree-zero root subgroup exactly, as `w*delta_0+(1-w)*Haar`, using no parabolic dynamics.
  corona-representations-are-exact-on-locally-finite-subgroups: that is the representation-level exactness lemma and the norm-2 dichotomy; this is the trace-level classification, and the two together say a nontrivial corona representation is coordinatewise a faithful representation of `SL_(12*2^m)(F_2)` whose normalized character on every fixed element tends to one constant `w<1`.
  leavitt-one-compressor-defect-lies-in-amenable-subgroups: that fences amenable subgroups containing the defect; this is a positive rigidity theorem about characters of the locally finite core, which holds in those amenable subgroups too and therefore cannot by itself close the endpoint.
  degree-zero-leavitt-core-has-locally-finite-marked-models: that gives exact finite models of finite windows of the core; this classifies the characters of the whole infinite core.
---

**ESTABLISHED.**  Let `R=L_(F_2)(1,2)`, let `R_0=union_m B_m`,
`B_m~=M_(2^m)(F_2)`, be the gauge-degree-zero core, and for `n>=3` put

```text
Gamma_0^(n)=EL_n(R_0)=union_m SL_(n*2^m)(F_2),                          (DHM1)
```

with the inductive embeddings `A -> A tensor 1_2`.  Let `phi` be any
character of `Gamma_0^(n)`: a normalized positive-definite class function.
Then there is `w in [0,1]` with

```text
phi(g)=w   for every g!=1 in Gamma_0^(n),        i.e.  phi=w*1+(1-w)*delta_e.   (DHM2)
```

Consequently:

1. For every character `phi` of the Leavitt group `H=EL_n(R)` (in
   particular every MF character, i.e. every pointwise limit of normalized
   traces of operator-norm asymptotic unitary representations), the
   restriction to `Gamma_0^(n)` is `w*1+(1-w)*delta_e`, and the same `w`
   governs every degree-zero subgroup: `phi(g)=w` for all
   `1!=g in Gamma_0^(n)`.
2. On every degree-zero root subgroup `x_ij(B_m)~=(F_2)^(4^m)`, the
   spectral measure of `phi` is exactly

```text
w*delta_0+(1-w)*Haar   on   (B_m)^* .                                   (DHM3)
```

   Thus the "Haar row profile" is not one bad case among many: it is the
   only possible nontrivial restriction, with a single free parameter.
3. `phi` is trivial on `H` iff `w=1`, i.e. iff `phi(g)=1` for ONE
   nonidentity degree-zero element, e.g. the manuscript defect
   `d=x_02(q)`.  Hence `Rad_MF(H)=H` holds as soon as every MF character
   has `w=1`.  Conversely, simplicity and
   `torsion-normal-generator-mf-character-criterion` turn any nontrivial
   corona representation into an MF character with `w<1`.

## Why the tensor tower is rigid while the corner tower is not

The argument uses only the inductive embedding of `(DHM1)`: an element
`A in SL_(n*2^m)(F_2)` becomes `A tensor 1_(2^(M-m))` in
`SL_(n*2^M)(F_2)`.  Its largest-eigenspace support is
`2^(M-m) supp(A) >= N/(n*2^m)`, a fixed positive fraction of
`N=n*2^M`.  By
`dense-support-character-ratios-of-sl-n-2-vanish` every nontrivial
irreducible character ratio at such an element tends to `0` as `M` grows,
so a character can see only the trivial weight.  A "corner" tower
`A -> A directSum I` would keep the support fixed and admits the full
Skudlarek--Thoma family of characters; the manuscript compressor `tau` is
not needed for `(DHM2)` and adds nothing to it.

## What this does and does not give for the Property-`(T)`-free endpoint

It pins the trace profile of every surviving corona representation to a
single number `w<1` on the whole degree-zero core, at every root, at every
depth: coordinatewise, the exact representations of `SL_(n*2^(m_k))(F_2)`
are `w`-trivial plus a part whose normalized character on every fixed
element vanishes in the limit.  It does NOT exclude that profile: the
regular representation of the finite groups realizes it, and the amenable
subgroups of `leavitt-one-compressor-defect-lies-in-amenable-subgroups`
carry norm-corona representations with exactly this profile and the
defect surviving.  The Property-`(T)`-free collapse is therefore
equivalent to the single statement

```text
no operator-norm asymptotic representation of H has
normalized trace tending to w+(1-w)*delta_e on Gamma_0 with w<1,     (DHM4)
```

and by `(DHM3)` any such representation has exactly Haar spectral profile
on every degree-zero root at every depth.

For the nonhyperlinear endpoint, this restriction theorem does not turn an
arbitrary non-Connes-embeddable character into a nonembeddable canonical
character. The linked character-transfer audit proves the valid conditional
implication: a full-group character simplex `conv{1,delta_e}`, together with
an actual nonembeddable character of that same group, forces
nonhyperlinearity. Neither additional input is supplied here. The audit
also gives a hyperlinear overgroup of this degree-zero core carrying a
nonembeddable character with canonical core restriction, and an explicit
two-generator abelian subgroup of `EL_3` whose character cannot extend
tracially because ambient conjugacy identifies elements it distinguishes.
These delimit restriction and extension arguments; they do not exclude a
future full-group theorem using the Leavitt group's additional structure.

No Property `(T)`, spectral gap, or stability theorem is used; the only
literature input is the finite-group character bound cited in
`dense-support-character-ratios-citation`.

No Steinberg-group extension is asserted here.  That extension needs a
separate unstable Morita/block-flattening theorem for
`St_n(M_k(F_2))` and compatible filtered-colimit embeddings.

DERIVATION
degree-zero-core-dirac-haar-proof
