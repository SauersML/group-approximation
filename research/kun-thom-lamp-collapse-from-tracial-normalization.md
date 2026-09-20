---
rg: 2
id: kun-thom-lamp-collapse-from-tracial-normalization
kind: route
title: "Universal tracial normalization collapses the marked binary Kun-Thom lamp product"
target: kun-thom-lamp-wreath-is-not-hyperlinear
requires:
  - kazhdan-compression-pairs-normalize-all-tracial-models
  - kun-thom-nonsofic-wreath
artifacts:
  - research/artifacts/liu-internality-normalization-audit-2026-09-20.md
---

## Attribution

The analytic input is Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf) (2026-09-20), Theorem 1.2 / 6.7; the explicit wreath obstruction is his Theorem 8.3. The conditional normalization/double construction is credited to Andreas Thom, and the pair and lamp construction to Gábor Kun and Andreas Thom, as Liu credits them. This node is a conditional specialization or downstream application through the named Cairn prerequisites, not a claim of independent discovery of Liu's theorem.

Use exactly the target's specialization `q=2`, `r=d=3`:

```text
Gamma=EL_3(F_2[x_1,x_2,x_3]),
G=EL_3(F_2[x_1^(+-1),x_2^(+-1),x_3^(+-1)]) rtimes SL_3(Z),
W=(direct_sum_(G/Gamma) C_2) rtimes G.
```

Theorem E, recorded in `kun-thom-nonsofic-wreath`, gives that `Gamma` and
`G` are Kazhdan and that the compression semigroup of `Gamma` generates
`G`. Discrete Kazhdan groups are finitely generated. Express a finite
generating set of `G` by words in compressors and their inverses; the
finitely many compressors occurring give the finite list required by
`kazhdan-compression-pairs-normalize-all-tracial-models`.

Put `t=(I,I+E_12)` and `gamma_0=(I+x_2 E_12,I)`. The substitution for `t`
sends the polynomial ring to `F_2[x_1,x_1 x_2,x_3]`. Its monomials have
first exponent at least second exponent, so it does not contain `x_2`.
Every entry of a matrix in `t Gamma t^-1` lies in this subring. Consequently
`gamma_0` belongs to `Gamma` but not `t Gamma t^-1`, and the cosets
`gamma_0 t Gamma` and `t Gamma` differ. Their binary lamp product

```text
b=a_(gamma_0 t Gamma) a_(t Gamma)
```

is nonidentity. The rings, actor, coset set, and finite-support lamp group
are countable, so `W` is countable.

Let `rho:W->U(M)` be any homomorphism into any specified tracial matrix
ultraproduct. There is no trace or injectivity assumption. Set
`D=rho(Gamma)' cap M`. Normalization applied to `rho|G` gives that `rho(G)`
normalizes `D`. The base lamp lies in `D`, since `Gamma` fixes its coset.
Hence `rho(a_(t Gamma))` lies in `D` and commutes with `rho(gamma_0)`.
Lamp covariance therefore gives

```text
rho(a_(gamma_0 t Gamma))=rho(a_(t Gamma)),   rho(b)=I.
```

This proves the universal marked collapse in the target and excludes an
injective homomorphism, proving nonhyperlinearity.

For completeness, it also supplies the target's finite obstruction. Present
`W` using symbols `s_g` for all `g in W`, and relators `s_e` and
`s_g s_h s_(gh)^-1`. They are countably many words of length at most three.
Some finite relator set `R_0` and `delta>0` force `||U_(s_b)-I||_2<=1` in
every dimension whenever their defects are less than `delta`. Otherwise,
exhaust the relators and choose increasingly accurate counterassignments;
their bounded unitary classes give a homomorphism from `W` to a tracial
matrix ultraproduct with `||rho(b)-I||_2>=1`, contradicting the collapse.

Let `F` be the symmetric closure of the identity, the group images of all
symbols in `R_0` and `s_b`, and every prefix of their displayed words. Put
`eta=min(delta/12,(sqrt(2)-1)/6)`. If an identity-preserving map on `F` has
every multiplicative defect and every separation deviation from `sqrt(2)`
strictly below `eta`, assign its values to those symbols and identity to
all others. Inverse and prefix comparisons give
`||v(U)-phi(vbar)||_2<=2|v|eta`. Thus each relator defect is at most
`6 eta<=delta/2`, whereas the distinct pair `b,e` forces
`||U_(s_b)-I||_2>sqrt(2)-3 eta>1`, a contradiction. This proves the stated
existence of dimension-independent `F,eta`, without asserting an effective
enumeration of them.

The route is conditional on universal tracial normalization. It imports no
unreviewed theorem from Liu as an empty-premise assertion.
