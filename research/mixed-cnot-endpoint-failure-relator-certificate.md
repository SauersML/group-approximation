---
rg: 2
id: mixed-cnot-endpoint-failure-relator-certificate
kind: claim
title: Charge the three mixed-CNOT endpoint failures by fixed group relators
distinct_from:
  robust-rank-one-endpoint-marginal-floor: that lower-bounds the sum of three abstract failure measures; this must upper-bound the concrete failures produced by the mixed router using a sparse relator certificate.
  c18-source-cut-has-sparse-relator-certificate: that certifies one ordered Boolean source-cut polynomial; this must certify three transported flag contexts while keeping the allowed K=+1 sector exact.
---

For the three endpoint-sharing mixed-CNOT contexts, express their diagonal and
crossed failure block operators as fixed sparse sums

```text
A_ij(U)=sum_t lambda_t V_t(U)(r_t(U)-I)W_t(U),          (MEF1)
```

with dimension-independent coefficient weight and fixed group relators
`r_t`.  The certificate must vanish on every allowed `K=+1` character, must
identify the crossed `K=-1,b=-1` block with the E5 hard exit, and must return
the complementary `K=-1,b=+1` block to the next active chart.

Together with sparse-certificate Cauchy--Schwarz, `(MEF1)` would bound the sum
of contextual failure masses by fixed normalized-HS energy and close
`mixed-cnot-joint-exit-first-hit-transducer`.

No such certificate is proved yet.  A scalar word in `K,b` is forbidden by
the two false-support tests recorded in that target; the certificate must use
the full endpoint transports.

This target is now refuted in its stated relator-ideal form.
`mixed-central-router-adjoins-without-collapsing-packet` embeds the finite
router packet, and each named failure block is a nonzero packet projection on
one of its marked simples. By
`embedded-packet-projection-has-no-relator-ideal-certificate`, an identity
`(MEF1)` would make that projection zero in the group algebra. The left
regular representation gives the same contradiction analytically: every
relator defect vanishes while the packet projection has positive `L^2` norm.

The repair is not a more elaborate elimination certificate. The failure
blocks must remain positive source mass and be transported into a globally
capacity-limited exit family. This is the role of
`full-v4-latent-coordinate-has-an-operator-five-fourths-floor` and
`global-v4-exit-capacity-is-cross-gram-curvature`.

## Attempts

- Direct expansion in the commuting signs `K,b` recreates the nonlinear AND
  and cannot be a group word.
- **Sparse relator elimination. Impossible.** Unlike the C18 difference,
  which is zero as a Boolean operator identity, a contextual failure block is
  a nonzero projection of the injectively embedded router packet. It cannot
  lie in the defining-relator ideal.
