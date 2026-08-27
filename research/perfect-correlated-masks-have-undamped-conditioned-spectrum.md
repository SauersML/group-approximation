---
rg: 2
id: perfect-correlated-masks-have-undamped-conditioned-spectrum
kind: claim
title: Every perfectly complete correlated mask is supported on the honest-spectrum annihilator and leaves its Fourier characters undamped
artifacts:
  - research/artifacts/perfect-correlated-mask-fourier-no-go-2026-08-21.md
distinct_from:
  reverse-kleene-does-not-remove-tv-completeness-loss: that identifies the global proof-gap crossing left by near-completeness; this rules out the only local distributional attempt to restore perfect completeness while retaining the published decoder.
  linear-encoding-lcs-admits-odd-subset-cheats: that describes all noise-free odd-character solutions algebraically; this proves the Fourier form for an arbitrary finitely supported correlated mask distribution.
  perfect-completeness-constant-soundness-lcs-compiler: that remains open for a different test or native LCS gap; this is a no-go only for changing the mask law in the Taller--Vidick long-code architecture.
---

Fix a conditioned satisfying set `C` and an honest spectral support `S` in
`C`.  Let `p_mu` be an arbitrary finitely supported, possibly correlated,
distribution on masks `mu:C->{+1,-1}`.  Perfect completeness is equivalent
to the linear constraints

```text
p_mu>=0,   sum_mu p_mu=1,
sum_mu p_mu (1-mu(phi))/2=0       for every phi in S.     (PCM1)
```

Since every summand is nonnegative, `(PCM1)` forces

```text
supp(p) subset {mu:mu(phi)=1 for every phi in S}.         (PCM2)
```

This is the annihilator of the coordinate characters indexed by `S`.  Hence
for every Fourier set `beta subset S`, correlated or not,

```text
hat p(beta)=sum_mu p_mu prod_(phi in beta)mu(phi)=1.       (PCM3)
```

Taller--Vidick conditioning places every decoded Fourier set inside `C`.
If perfect completeness is required for every satisfying long-code dictator,
then `S=C`, so every Fourier coefficient surviving the conditioning step is
exactly undamped.  The best possible distribution is Haar noise off `C`, but
that noise is invisible to the decoder.

More quantitatively, any decoder comparison

```text
|beta|^(-1/2) >= c |hat p(beta)|
```

has `c^2<=1/|S|` by taking `beta=S`.  In the `u`-fold source,
`|S|` can grow as `m^u`; this is no better than the source game's universal
random-guessing floor `m^(-u)` and cannot yield the strict soundness
comparison.  Thus finite support and arbitrary correlations do not repair
the endpoint.

The proof and the exact linear/Fourier calculation are in
`perfect-correlated-mask-fourier-no-go-proof`.

**Note (2026-08-22 audit).**  `linear-encoding-lcs-admits-odd-subset-cheats`
is OPEN again: its global statement fails for sources with non-extendable
local assignments (`odd-subset-relaxation-needs-local-extendability`);
any "encodings cannot create LCS hardness" / "dies by the odd-subset
cheat" reasoning here holds only under local extendability of the source.
