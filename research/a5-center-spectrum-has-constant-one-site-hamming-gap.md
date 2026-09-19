---
rg: 2
id: a5-center-spectrum-has-constant-one-site-hamming-gap
kind: claim
title: The regular A5 packet center charges one wrong site permutation by constant Hamming mass
distinct_from:
  simple-lamp-normalizers-have-unitary-multiplicity-fibers: that identifies the arbitrary unitary fiber after fixing a packet automorphism; this passes to the center, where that fiber disappears, and computes the resulting metric obstruction.
  simple-lamp-hyperlinear-recovery-forces-action-sofic: that is the desired global recovery implication; this proves that using regular-packet centers cannot tolerate the partial-site boundary left by finite lamp windows.
  partial-schreier-completion-preserves-sofic-loss: that completes partial permutations when the missing domain has small uniform site density; the Plancherel center metric here assigns a constant cost even to one wrong site.
---

ESTABLISHED.  Let `K=A5`, let `Q=K^F`, and give the center spectrum of the
left regular representation of `Q` its normalized-rank measure.  Canonically

```text
Omega_F = Irr(K)^F,
mu_F = p^F,
p_pi = dim(pi)^2/60.                                    (ACS1)
```

Every automorphism of `Q` acts on `Omega_F`; the arbitrary right-regular and
external-multiplicity unitary in
`simple-lamp-normalizers-have-unitary-multiplicity-fibers` acts trivially
there.  Nevertheless, if two automorphisms induce different permutations of
the coordinate factors, their center permutations have weighted Hamming
distance at least

```text
1-sum_(pi in Irr(A5)) p_pi^2
 = 1-(1+81+81+256+625)/3600
 = 71/100.                                               (ACS2)
```

The bound is independent of `|F|` and of every external multiplicity.
Consequently the center does recover the site permutation of a **complete
invariant packet**, but it does not turn the partial factor maps from a finite
lamp window into a sofic-scale approximation.  Two proposed completions which
disagree at even one site remain at center-Hamming distance at least `71/100`.
Thus vanishing center defect requires an exactly coherent completion on every
packet factor once the defect is below this constant; an `o(|F|)` site
boundary is not diluted.

There is a second obstruction to using individual central fibers as the
Definition-4.23 chart states.  A central fiber `omega in Omega_F` is faithful
on `K^Z`, for `Z subset F`, exactly when every coordinate label `omega_z` is
nontrivial.  Since the trivial representation has Plancherel mass `1/60`,

```text
mu_F{omega : omega|_(K^Z) is faithful}=(59/60)^|Z|.      (ACS3)
```

For a fixed nonempty chart window this good-state density is bounded away
from one, and it worsens with `|Z|`; amplification of the regular
representation does not change `(ACS1)`.

Hence intrinsic minimal normal factors and regular-packet centers locate the
boundary sharply:

1. factor labels recover exact partial site maps without monomializing the
   multiplicity space;
2. the center kills the arbitrary unitary fiber for a globally normalized
   packet;
3. but finite-window covariance supplies no invariant global packet, and the
   center metric makes a single boundary/completion mismatch macroscopic;
4. passing to individual sectors instead loses the injectivity density
   required of action charts by `(ACS3)`.

Any positive `A5` recovery theorem must therefore construct a coherent
near-total copy/state action before taking centers, or add a genuinely new
equivariant bundling/classicalization mechanism.  Minimal normality or the
center spectrum alone does not supply that missing completion.

