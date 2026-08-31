---
rg: 2
id: kun-thom-clifford-crossed-product-ce
kind: claim
title: Connes embeddability of the Kun--Thom Clifford crossed product
artifacts:
  - notes/TRUE_KUN_THOM_CLIFFORD_PHASE.md
  - notes/FALSE_FERMIONIC_KUN_THOM_ENDPOINT.md
---

For the explicit residually finite nonnormal infranormal Kazhdan pair
`Gamma<G`, prove that the canonical tracial algebra

```text
Cl(G/Gamma) crossed_product G
```

is Connes embeddable.  The Clifford base is hyperfinite, but arbitrary
crossed-product permanence is unavailable and the coset action is the
nonsofic action at the heart of the Kun--Thom theorem.

## Ideas

**Position in the lane.**  This claim is the *strongest* member of a chain
whose weakest member already answers Q3.4:

```text
kun-thom-clifford-crossed-product-ce
  => kun-thom-clifford-relative-wall   (anticommuting wall)
  => bare-relative-wall-exists          (v != pi(h) v pi(h)^*)
  => hyperlinear-nonsofic-group
```

and, by the diagonal doubling `c_x tensor c_x` of
`TRUE_DOUBLE_CLIFFORD_KUN_THOM_REDUCTION.md`, it also implies Connes
embeddability of `L(W)=L^infinity({-1,1}^(G/Gamma)) crossed_product G`, i.e.
hyperlinearity of the Kun--Thom wreath group itself.  No reduction runs
backwards.  Effort spent here buys everything, but it is priced accordingly;
`bare-relative-wall-exists` is the cheapest sufficient statement in the lane
and is now a first-class node.

Two of the apparent extra costs are now known to be illusory or real:

* the *trace energy* of the wall is free (`wall-energy-amplification`:
  diagonal tensor powers push any wall to squared energy `>=2`);
* the *anticommutation* is not free.  Amplification gives
  `v_k w_k=(vw)^(tensor k)`, so the Clifford sign is a genuine strengthening.
  The precise gap between `bare-relative-wall-exists` and the Clifford wall
  is: can a bare wall be "Clifford-ified"?  That is the one question whose
  answer would collapse this claim's lane onto the cheapest one.

**Why the Clifford lane exists at all.**  Kun--Thom Corollary D says the
generalized Bernoulli p.m.p. action `G -> (K,kappa)^(G/Gamma)` is not sofic,
and the Cartan/chart reverse-transfer kills every coordinate model of `L(W)`.
`Cl(X)` is a factor with no `G`-invariant Cartan, so there are no coordinates
to pull the chart obstruction back along.  That is a constructive advantage
only; logically the Clifford claim is above the Bernoulli one.

**Status of the trace-blindness question.**  Yes, trace-blindness works *for*
this program, but only defensively and only so far:

* the finite-dimensional/profinite route is dead
  (`infranormal-compact-closure-normal`): in every compact image the closure
  of `Gamma` is normal, so the quasi-regular first chaos is not even a
  pointed weak limit of finite-dimensional representations;
* the mechanism that kills it is a cardinality count — isotropy orders and
  orbit cardinalities in Kun--Thom Theorem 4.1, linear dimension in
  `commutant-no-growth` — and that count has *no informative normalized
  shadow* (`commutant-density-trace-blind`: the normalized commutant density
  is a character invariant, hence exactly equal for `Gamma` and
  `t Gamma t^(-1)`, and identically `0` for every model in play);
* the surviving II_1 substitute is the Pimsner--Popa index
  (`relative-wall-commutant-growth`, Corollary 5), and
  `clifford-compressor-site-growth` computes it inside `M_Cl`: infinite at
  every strict positive compressor, with the new Clifford modes indexed by
  `L_+ minus L_+ s`, the failure of right divisibility in the compression
  monoid.

So no counting invariant can refute this claim; a refutation must come from
flexible normalized-Hilbert--Schmidt stability of `G` (or already of the
ascending HNN subgroup `<Gamma,t>`), which restores an exact representation
and with it the exact count.  That is the fork, and it is genuinely open:
the known 2-Kazhdan/cohomological results give *unnormalized Frobenius*
stability, which is on the wrong side of the normalization firewall
(`TRUE_CLIFFORD_HYPERLINEARITY_FORCES_AMBIENT_HS_INSTABILITY.md`, Section 4).

**What the shape of the required model is.**  The tower
`N < Ad pi(t)(N) < Ad pi(t)^2(N) < ...` demanded by Corollary 5 has infinite
index at every step in `M_Cl`.  That shape is harmless on its own: the
one-sided Clifford shift `c_n |-> c_(n+1)` is an infinite-index endomorphism
of the hyperfinite II_1 factor, so an infinite-index compressor tower already
exists inside `R`.  What is missing is coherence of the tower with the whole
property-`(T)` group, i.e. the coherent Bogoliubov-innerness problem
`(DCK15)`.  Any construction attempt should start from a shift on a
one-sided Clifford half-space carrying the `L_+`-indexed site set of
`clifford-compressor-site-growth`, and the difficulty should be located
exactly at the elements of `L` that leave `L_+`.

**Dead, do not redo:** honest finite-dimensional/compact Bogoliubov models
(`infranormal-compact-closure-normal`); Gaussian second quantization of
`lambda_(G/Gamma)` (the Gaussian action *is* a generalized Bernoulli action,
so Kun--Thom Corollary D plus the Hayes entropy computation excludes full
Wick-moment models); Definition-4.23 chart models with any target class
(`lamp-charts-recover-set-action`, route `halo-chart-clifford-model`); exact
`G`-invariant AF/profinite filtrations
(`profinite-action-fixed-algebra-invariant`, route
`profinite-clifford-filtration`); operator-norm/weak-MF certificates (the
central sign is invisible there — `central-sign-corona-obstruction`,
Proposition 8 of the perfect-core note); any model whose commutant growth is
finite index at a positive elementary transvection (Corollary 7 of the wall
note, and `clifford-compressor-site-growth` for the values).

**Do not re-open as separate routes:** the full Majorana crossed product, the
even CAR core, and a Connes-embeddable character seeing `z` are one problem
(`clifford-ce-targets-are-equivalent`), and an operator-norm certificate for
them is impossible, not merely unavailable
(`kun-thom-clifford-extension-not-weak-mf`).  The Bernoulli corner is *implied* by
this one (`clifford-ce-implies-bernoulli-ce`), so this claim is equivalent to
hyperlinearity of the whole cover `Wtilde`, and the deduction chain down to
Q3.4 is `thom-central-corner-criterion` (Thom Lemma 3.3 and Remark 3.4,
source-verified) or, more cheaply, the radical collision, which needs no
central-quotient theorem at all.

**Cheaper instances worth preferring.**  `invariant-graph-crossed-product-ce`
asks only for *some* nondegenerate `G`-invariant graph, not the complete one;
`notes/NOTEPAD.md` (near line 9969) gives the concrete sparse instance, the
orbital graph of one symmetric double coset, whose `z=-1` lamp algebra is the
AF twisted algebra `C_r^*(directSum_X F_2,(-1)^(B_*))` and whose Bogoliubov
action is far more local than the complete one.  If a construction is going
to be attempted at all, attempt it there.

*(2026-08-18.)*  That instance is now a first-class node,
`minimal-marked-graph-crossed-product-ce`, and its algebraic prerequisite is
discharged: `minimal-marked-graph-nondegenerate` proves the minimal marked
orbital graph has zero radical, so its lamp algebra is the hyperfinite
factor and no graph search is left.  Prefer it over this claim: it is
strictly weaker, it targets a named algebra, and its finite-window form has
the lamp side solved exactly (`vertex-supported-symplectic-completion`), so
all of its content sits in the coherence of the implementers.
