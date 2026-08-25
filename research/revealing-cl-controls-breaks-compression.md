---
rg: 2
id: revealing-cl-controls-breaks-compression
kind: claim
title: Revealing CL controls linearizes one fiber but breaks recursive compression
distinct_from:
  jnvwy-canonical-halt-strategy-is-affine-unsafe: that exhibits the odd-xor violation produced by the unrepaired sampler; this proves why exposing its local control is not a polynomial-size repair after repetition.
  dfnqxy-halt-completeness-support-is-not-canonically-specified: that leaves open a different perfect HALT strategy; this audits one proposed modification of the JNVWY introspection construction itself.
  affine-halt-support-and-pcpp-section-close-nonhyperlinear-chain: that gives a conditional endpoint from affine-safe HALT supports; this identifies the new introspection theorem that would be needed to obtain those supports by control revelation.
---

**ESTABLISHED NO-GO FOR CLASSICAL CONTROL REVELATION.**  The nonlinear
axis-line component isolated in
`jnvwy-canonical-halt-strategy-is-affine-unsafe` is linear on each fiber of
its small control.  Nevertheless, revealing those controls as verifier
questions cannot repair the recursive JNVWY construction within its stated
complexity bounds: after anchored repetition, affine safety forces the
question to distinguish exponentially many control profiles.

## One axis-line coordinate can be repaired

Use the notation of equation (30) of arXiv:2001.04383v3:

```text
L_A(u,s,v)=(L^lnf_(e_(chi(s)))(u),s,0),                (RCL1)
```

where `q=2^k`, `m=2^j`, and `chi(s)` records the interval of length `q/m`
containing the integer representative of `s`.  In the paper's fixed binary
basis, a fiber `chi(s)=i` is an affine subspace: it fixes the high `j` bits of
`s` and leaves the low `k-j` bits free.  On this fiber the selected deletion
map is fixed, so `(u,s,v) -> (L^lnf_(e_i)(u),s,0)` is the restriction of one
linear map.  Thus sending either all of `s` or just `chi(s)` in the verifier's
question makes the honest graph support affine in this one coordinate.

This observation does not alter the soundness proof for one coordinate.  It
only conditions the existing sampling test on classical data which the
verifier already computes.  The obstruction is its size after repetition.

## Distinct repeated profiles cannot share one affine-safe question

Let `A=L^lnf_(e_1)` and `B=L^lnf_(e_2)`.  Restrict every repetition coordinate
to controls selecting only `A` or `B`.  Consider any proposed external
question value whose conditional honest support contains two distinct
profiles `alpha,beta in {A,B}^K`.  Choose a coordinate `r` where they differ,
and orient the notation so that `alpha_r=A`, `beta_r=B`.  In coordinate `r`
take payload `e_2`, while fixing all other payloads to zero.  The conditional
support then contains the three graph points

```text
(alpha,0,0),  (alpha,e_2,A(e_2)),  (beta,0,0).          (RCL2)
```

Their odd xor has control profile `beta`, payload `e_2`, and claimed output
`A(e_2)`.  But `A(e_2)=e_2` and `B(e_2)=0`, so this xor is rejected by the
graph test for profile `beta`.  Hence no affine-safe conditional support can
mix `alpha` and `beta`.

It follows that a classical control-revelation repair must distinguish all
`2^K` profiles even after this two-choice restriction.  Its question needs at
least `K` control bits.  Revealing one randomly selected control, a checksum,
or any label with fewer than `K` bits leaves two profiles in one fiber and the
same witness applies.

## This violates the introspection/compression complexity theorem

Section 11.3 defines anchored repetition using

```text
K(N)=(lambda N)^((1+c') tau)                           (RCL3)
```

(up to the harmless renaming of the repetition exponent in the summary of
`Compress`).  In one recursive compression at output index `n`, introspection
is applied to the source verifier at `N=2^n`.  Therefore the required exposed
profile has length

```text
K(2^n)=(lambda 2^n)^((1+c') tau)=2^(Omega(n)).         (RCL4)
```

The Introspection Theorem requires
`TIME_(sampler^intro)(n)=poly(n,lambda,ell)`.  A sampler cannot even write the
profile in that time.  Thus the modified verifier is not the question-reduced
normal-form verifier asserted by that theorem, and the recursive Compression
Theorem no longer has polynomial verifier complexity.

Turning profiles into types is not an alternative.  The detyping construction
uses ambient dimension `4|type|+s` and its soundness loss is
`16^|type|`.  A type for every repeated control profile makes both parameters
exponential (indeed the soundness factor is doubly exponential in `K`).

## Exact missing replacement

The narrow repair would require a new **affine-fiber introspection lemma**.
For the repeated source sampler it would have to

1. use only `poly(n,lambda,ell)` question bits and sampling time;
2. introspect the full product CL distribution needed by the source verifier;
3. make every honest `Intro--Sample` support an accepted affine fiber; and
4. retain the robust soundness and entanglement extraction of the
   Introspection Theorem.

The counting argument above rules out obtaining such a lemma merely by
classically revealing `s`, `chi(s)`, or any lossless encoding of the existing
coordinatewise controls.  A successful repair must replace the repeated
sampler/encoding or prove affine safety by a different perfect strategy; it
is not a local change to the verifier's question format.
