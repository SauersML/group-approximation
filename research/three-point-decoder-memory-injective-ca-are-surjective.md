---
rg: 2
id: three-point-decoder-memory-injective-ca-are-surjective
kind: claim
title: An injective automaton with a three-point left-inverse memory is surjective, over every group
distinct_from:
  amenable-decoder-memory-forces-surjectivity: that proves surjectivity when the decoder memory generates an amenable group, which covers every two-point decoder memory; this is the first case it leaves open, three points generating a nonamenable group.
  three-address-binary-injective-rules-are-balanced: that bounds the encoder memory, the addresses the rule reads, over the binary alphabet; this bounds the decoder memory, for any alphabet and any encoder memory.
artifacts:
  - research/artifacts/random-order-decoder-transport-2026-09-12.md
---
**OPEN.** Let `G` be any group, `A` a finite alphabet, `tau` an injective automaton on `A^G` with any memory, and
`sigma` an automaton with `sigma tau = id` and memory `N = {e, s, t}`. Then `tau` is surjective.

When `<s, t>` is amenable this is `amenable-decoder-memory-forces-surjectivity`. So the content is the case
`<s, t>` nonamenable, which that theorem shows every strict pair must reach.

## Attempts
- **Transport form** (artifact 3.3). By `injective-ca-random-order-transport-identity`, the three transport terms
  into `y(e)`, from the input sites `e, s^-1, t^-1`, sum to `log |A|`. Surjectivity is equivalent to their sum being at
  most `H(y(e))` for the automaton amplified by
  `strict-automata-give-injective-ca-with-skewed-site-marginals`. That amplification may enlarge the decoder
  memory, and checking whether it keeps three points is the first step.
- **Where group structure enters.** The conditionings live at the seven sites
  `{s, t, s^-1, s^-1 t, t^-1, t^-1 s, e}`. Relations of `<s, t>` act only by making some of these sites coincide, so the
  inequality can be tested relation by relation. The free case `<s, t> = F_2` is sofic, hence already true. The
  question is whether it holds for a reason that uses no finite model.
- **Pointwise versions fail.** A single order realization can violate domination even for bijective automata
  (artifact 3.2). Averaging over the random order is required.
- **Transport gives only a reciprocal bound** (`transport-identity-gives-reciprocal-memory-entropy-bound`,
  e87f4c60f5). The identity plus the per-term bound `I(.;y(e)|.) <= H(y(e))` yields only
  `H(y(e)) >= (log |A|)/3`; the per-term bound is tight, so no term-by-term argument reaches domination. A proof must
  use realizability (`y` a finite block code of i.i.d. `x`), not only the information relations at the seven sites.
- **Amplification does not reduce this claim** (`skewed-marginal-amplification-enlarges-decoder-memory`, e87f4c60f5).
  The skewed amplification of a strict `tau` has left-inverse memory `N_tau ∪ W_anchor ∪ W_block`, not three points,
  so three-point domination does not feed the surjectivity reading by amplification. Read the claim either as the
  `h_fin` statement for three-point-decoder automata, or attack single-site domination for the enlarged-memory `kappa`.
- **Caution on the free case.** "The free case `<s,t> = F_2` is sofic, hence already true" is about soficity of the
  decoder memory group, not of the host `G`. The coset argument of `amenable-decoder-memory-forces-surjectivity`
  reduces it to pre-injectivity of a surjective automaton over `F_2`, and GOE's surjective-implies-pre-injective
  direction fails on `F_2` (Bartholdi). So the free-`Gamma` case needs its own justification and should be treated as
  open; the amenable mechanism closes exactly the amenable-`<s,t>` cases.
