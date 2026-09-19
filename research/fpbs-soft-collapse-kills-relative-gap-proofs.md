---
rg: 2
id: fpbs-soft-collapse-kills-relative-gap-proofs
kind: claim
title: Over invariant sparse spines the soft collapse family meets every infinite subgroup infinitely just above p_c, so no soft argument proves any relative threshold gap, even on pairs where the gap is true
distinct_from:
  fpbs-soft-collapse-iff-invariant-sparse-spines: that kills soft proofs of p_c < p_u; this kills soft proofs of the intermediate statement p_c < p_c(I;G) along any infinite subgroup, which that obstruction does not reach, because the passage from a relative gap to p_c < p_u uses Hutchcroft--Pan facts about Bernoulli percolation above p_c.
  fpbs-soft-collapse-on-fg-normal-and-kazhdan-groups: that is the OPEN extension of the spine class; this uses only the ESTABLISHED Z-quotient spines, and records the larger class only conditionally.
  fpbs-relative-susceptibility-divergence-crux-fails: that shows critical relative finiteness does not force a gap on trees with amenable quotient; this shows that no set of Bernoulli facts at p <= p_c, whatever they are, forces a gap once supercritical inputs are soft, including on pairs with nonamenable quotient.
  fpbs-invariant-schur-weights-cannot-certify-critical-l2: that kills invariantly produced Schur weights for the critical L2 bound; the weight remark here concerns tilted relative susceptibilities, and is recorded only as a remark.
---

**ESTABLISHED (class-killing obstruction).** Proof route
`fpbs-soft-collapse-kills-relative-gap-proofs-proof`.

Terminology is that of `fpbs-soft-collapse-iff-invariant-sparse-spines`: soft
collapse family `(omega_t)` with axioms (S1)--(S4), invariant sparse spines.
For a random bond configuration `omega` and a subgroup `I <= Gamma` write
`chi^I(omega) = E|K_o(omega) ∩ I|`.

**Theorem.** Let `G = Cay(Gamma,S)` carry a soft collapse family
`(omega_t)`. Then for every `t > p_c(G)` and every infinite subgroup
`I <= Gamma`, normal or not,

```text
P( |K_o(omega_t) ∩ I| = infinity ) >= theta(t) > 0,   so   chi^I(omega_t) = infinity.
```

So the soft relative threshold `sup{t : chi^I(omega_t) < infinity}` equals
`p_c(G)` for every infinite `I`, while `(omega_t)_(t <= p_c)` is exactly
Bernoulli.

**Corollary (obstruction).** Suppose `G` has invariant sparse spines. Then no
argument whose inputs are (a) facts about Bernoulli percolation on `G` at
parameters `p <= p_c(G)` and (b) the supercritical properties (S1)--(S4)
can prove `chi^I_p < infinity` for some `p > p_c(G)`. So it cannot prove
`p_c(G) < p_c(I;G)` for any infinite subgroup `I`. In particular it cannot
prove `fpbs-percolation-kesten-normal-gap` or
`fpbs-percolation-schreier-kesten-gap` on `G`.

Inputs of type (a) include critical relative finiteness `chi^I_(p_c) < infinity`,
the uniform fibre bound, Hutchcroft--Pan relative sharpness below `p_c`,
critical fibre l2 where it holds, and the Russo--BK kernel at `p_c`.

- **Invariant:** existence of invariant sparse spines, i.e. of a unique
  infinite cluster in a coupled invariant family agreeing with Bernoulli up to
  `p_c`.
- **Step where every member dies:** the step that turns information at `p_c`
  into `chi^I_(p_c + delta) < infinity`. The proof shows that the unique
  infinite cluster meets `I` in an `I`-invariant random set. Every such set
  that is nonempty and finite has probability `0`.

**Pairs covered (unconditional).** By Theorem B of
`fpbs-soft-collapse-iff-invariant-sparse-spines`, `G` has spines whenever some
surjection `Gamma -> Z` has finitely generated kernel. The class contains these
Kesten-gap pairs, each with `Gamma/N` nonamenable:

1. `Gamma = F_2 x Z`, `N = {1} x Z`, `Gamma/N = F_2`, kernel of the
   projection to `Z` is `F_2`. This is a flagship-relevant pair: the gap along
   `N` is equivalent to `p_c < p_u` on these Cayley graphs, since `N` is
   amenable (`fpbs-amenable-wq-normal-pu-is-relative-pc`).
2. `Gamma = (Z/2*Z/2*Z/2) x Z`, i.e. `G = T_3 x Z` with product generators,
   `N = Z`, `Gamma/N` virtually free. **Here the gap is true**:
   `p_c(N;G) = p_h(G,Gamma_xi)` by
   `fpbs-tree-product-relative-threshold-is-heaviness-threshold`, and
   `p_c(G) < p_h` by Hutchcroft
   (`fpbs-hyperbolic-and-nonunimodular-nonuniqueness`). So the obstruction
   separates methods, not truth: any proof of the gap on `T_3 x Z` must use a
   property of supercritical Bernoulli percolation outside (S1)--(S4).
   Hutchcroft's nonunimodular argument must therefore be of that kind. It also
   uses the modular cocycle, which is the escape recorded in the remark below.
3. `Gamma = F_2 x F_2`, `N` either factor, `Gamma/N = F_2`. Spines exist
   because the kernel of the map `F_2 x F_2 -> Z` sending all four basis
   elements to `1` is finitely generated (Bieri--Stallings: that kernel is
   of type `F_1`, i.e. finitely generated, but not finitely presented; cited,
   not re-proved). This is the natural test case for a type-(ii) pair named in
   `fpbs-percolation-kesten-normal-gap`, Attempts.

**Pairs covered (conditional).** If `fpbs-soft-collapse-on-fg-normal-and-kazhdan-groups`
is established, the class widens to every nonamenable group with an infinite
finitely generated normal subgroup of infinite index, and to every infinite
Kazhdan group.

**What survives.** A proof of any relative gap on a spine group must use a
genuinely Bernoulli supercritical property: independence at `p > p_c`
(BK, Russo, Harris--FKG between increasing events at `p > p_c`), deletion
tolerance, or the product structure itself. Harris--FKG and deletion tolerance
are not decided for the collapse family, so they remain possible escape
inputs, as in the parent obstruction.

**Remark (weight tilts, not load-bearing).** On a unimodular Cayley graph,
let `w : Gamma -> (0,infinity)` be submultiplicative, `w(xy) <= w(x)w(y)`,
for instance `w = f o pi` pulled back from a length or exponential weight on
`Q = Gamma/N`. Then `X_p = sum_x tau_p(o,x) w(x) >= chi_p`. Indeed
`tau_p(o,x) = tau_p(o,x^(-1))`, and `w(x) + w(x^(-1)) >= 2 sqrt(w(x)w(x^(-1)))
>= 2 sqrt(w(e)) >= 2` because `w(e) <= w(e)^2`. So `X_(p_c) = infinity`.
Hutchcroft-type tilted susceptibilities that stay finite at `p_c` need a
cocycle such as `Delta^(1/2)`, which a unimodular graph does not have. They do
not need a weight function. So no weight on the quotient gives a finite tilted
quantity at `p_c` to integrate upward.
