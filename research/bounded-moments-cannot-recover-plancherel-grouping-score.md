---
rg: 2
id: bounded-moments-cannot-recover-plancherel-grouping-score
kind: claim
title: Bounded moments cannot recover the global Plancherel grouping score
artifacts:
  - research/regular-versus-steinberg-gives-moment-score-separation.md
distinct_from:
  plancherel-score-recovers-reducible-endpoint-grouping: that gives an exact dimension-free score from the full quotient multiplicity vector; this proves no fixed word-moment window can approximate that score uniformly as the quotient moves.
  bs14-bounded-moments-cannot-extract-congruence-level: that makes deep regular BS-core levels moment-indistinguishable; this gives same-dimensional exact whole-group endpoints whose regular-grouping scores stay maximally separated.
  steinberg-endpoints-are-indecomposable-but-payload-width-one: that isolates one Steinberg endpoint as quantum-indecomposable but captured; this amplifies it to the regular dimension and compares all bounded multiplication moments with the regular endpoint.
---

For odd primes \(p\geq5\), let
\[
 G_p=\operatorname{PSL}_2(\mathbb F_p),\qquad
 d_p=|G_p|,\qquad q_p=\frac{|G_p|}{p}=\frac{p^2-1}{2}.   \tag{BMS1}
\]
On the same dimension \(d_p\), form the exact congruence endpoints
\[
 R_p=\lambda_{G_p}\circ\operatorname{red}_p,\qquad
 S_p=(\operatorname{St}_p)^{\oplus q_p}
      \circ\operatorname{red}_p.                         \tag{BMS2}
\]

For every fixed finite word set \(W\subset A\), and more generally every
fixed finite family of bounded-degree noncommutative \(*\)-moments in the
marked group matrices,
\[
 \max_{w\in W}
 \left|\operatorname{tr}_{d_p}(R_p(w))
       -\operatorname{tr}_{d_p}(S_p(w))\right|
 \leq\frac1p                                             \tag{BMS3}
\]
for all sufficiently large \(p\). The same bound holds after replacing
\(W\) by the finite set of group words obtained by multiplying the entries
in any one fixed moment family.

Nevertheless their global regular regrouping scores satisfy
\[
 \mathfrak R_{G_p}(R_p)=0,\qquad
 \mathfrak R_{G_p}(S_p)=1.                               \tag{BMS4}
\]
Thus even exact multiplicativity, identical ambient dimension, and
asymptotically identical bounded-degree multiplication moments do not
determine the full Plancherel grouping vector.

There is also no unique modulus selector from bounded moments. Given two
distinct primes \(p,\ell\), amplify \(\lambda_{G_p}\) by \(|G_\ell|\) and
\(\lambda_{G_\ell}\) by \(|G_p|\). The two exact endpoints have the same
dimension and exactly the same normalized traces on every fixed word which
survives nontrivially in both quotients. As \(p,\ell\to\infty\), every fixed
nonidentity word has this property.

Consequently a quotient-table recovery theorem cannot use a fixed
relator/character window, even with exact input tuples. Its window or
operator-valued multiplication data must grow with the moving quotient, or
it must select adaptively using information beyond bounded scalar moments.
This is a selector firewall, not a capture counterexample: all tuples in
(BMS2) are already exact congruence endpoints. The root remains open.

DERIVATION
regular-versus-steinberg-gives-moment-score-separation
