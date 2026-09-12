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
- **Per-term bounds give only subadditivity** (`transport-identity-gives-reciprocal-memory-entropy-bound`). Bounding
  each transport term by `H(y(e))` and summing gives `H(y(e)) >= (log |A|)/3`. That is the elementary bound
  `log |A| <= H(y|_N) <= 3 H(y(e))` (direct proof by w3-vf-positive), so the identity adds nothing at that level. The
  sharper per-term bound gives `sum_n H(y(e) | Z_n, U) >= log |A|`, which is not domination because the conditionings
  differ. A proof has to use the three conditionings jointly. No Shannon-type proof was found, and none has been shown
  impossible. (Corrected at the second landing: the first entry said the per-term bound is tight and that a proof
  must use realizability; both are withdrawn.)
- **Amplification step: open** (`skewed-marginal-amplification-enlarges-decoder-memory`, OPEN). The decoder built in
  the skewed construction reads `N_tau ∪ W_anchor ∪ W_block`. The only proved lower bound is that any left inverse of
  the amplified `kappa` restricts to a left inverse of `tau` with contained memory (artifact Lemma 3.1). So the
  reduction above is not known to work: it needs a three-point left inverse of `kappa`, and whether one exists is
  open. (Corrected at the second landing: the first entry asserted the enlargement as established.)
- **Caution on the free case.** "The free case `<s,t> = F_2` is sofic, hence already true" is about soficity of the
  decoder memory group, not of the host `G`. Two gaps:
  - the amenable mechanism reduces the free case to pre-injectivity of a surjective automaton over `F_2`, where
    "surjective implies pre-injective" fails (attributed to Bartholdi; not re-read);
  - the joint law of `y` at the seven sites depends on the encoder windows, so relations of `G` outside `<s,t>` enter.

  So the free-`Gamma` case should be treated as open. The amenable mechanism closes exactly the amenable-`<s,t>` cases.
