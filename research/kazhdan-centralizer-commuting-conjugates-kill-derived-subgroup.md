---
rg: 2
id: kazhdan-centralizer-commuting-conjugates-kill-derived-subgroup
kind: claim
title: Commuting compressed conjugates kill every Kazhdan subgroup of the derived subgroup of a centralizer, with no local finiteness or normality
distinct_from:
  locally-finite-centralizer-derived-subgroup-is-mf-invisible: that needs the centralizing subgroup C locally finite and uses the exact correction of finite groups and finite averages; this allows C arbitrary, for example torsion-free, and replaces both finite devices by the Kazhdan spectral projection of a property-(T) subgroup D of [C,C] normalized by C, so it kills D instead of all of [C,C].
  normal-kazhdan-defect-non-mf: that needs a normal Kazhdan subgroup of the ambient group inside the defect; this needs no normal Kazhdan subgroup, only Kazhdan D inside the centralizer's derived subgroup, which is what lets it act inside infinitely generated lamp radicals.
  virtually-infranormal-kazhdan-mf-detection: that weakens normality of the killed Kazhdan subgroup to finite-index infranormality; here the killed subgroup D need not be infranormal in any finite-index subgroup, as in a lamp wreath where D sits at one site.
  sofic-groups-kill-rigid-compression-defects: that is a sofic kill of compression defects when the compressor group is Kazhdan; this is an MF kill, and item (KC3) records that the sofic kill makes this criterion vacuous exactly in that Kazhdan-compressor situation.
---

**ESTABLISHED.**  Let `G` be countable and suppose

```text
L <= G has property (T),   u in G,   u L u^-1 <= L,
C <= C_G(L),
[u C u^-1, ell u C u^-1 ell^-1] = 1   for some ell in L,         (KC0)
D <= [C,C],  D normalized by C,  D has property (T).
```

Then:

- **(KC1)** every operator-norm asymptotic unitary representation
  `V_n : G -> U(d_n)` satisfies `||V_n(h) - I|| -> 0` for every `h in D`.
  Equivalently, every homomorphism from `G` to a norm matrix corona kills
  `D`, and so does every homomorphism to an MF group:
  `<<D>>_G <= Rad_MF(G)`.
- **(KC2)** If `C` itself has property (T), take `D = [C,C]`.  This has
  finite index in `C`, so it is Kazhdan and normal in `C`.  Then
  `<<[C,C]>>_G <= Rad_MF(G)`, and `G` is not MF whenever `C` is
  nonabelian.
- **(KC3), where the criterion is vacuous.**  Suppose `G` lies in a sofic
  group `H`, and `u` lies in a Kazhdan subgroup `G_0 <= H` in which `L` is
  infranormal.  Then `u C u^-1` is abelian, so `[C,C] = 1` and (KC1) is
  empty.
- **(KC4), subsumption.**  Under (KC0), every commutator
  `[u c u^-1, u c' u^-1]` lies in the normal closure of the single-root
  defect `{[u c u^-1, l] : l in L}`.  Hence `[C,C] <= D_G(L)`.

  Suppose the ambient group has a normal Kazhdan subgroup `K` inside such a
  single-root closure.  For example, `K = <<[u c u^-1, u C u^-1]>>_G`.
  Then (KC1) for `K` already follows from `normal-kazhdan-defect-non-mf`.

  So the criterion is new only in two situations:
  - no normal Kazhdan subgroup is available, as in lamp radicals, which
    are infinitely generated;
  - several roots are needed.

**What changes.**  The locally finite criterion used local finiteness
twice:
1. to correct a fixed finite subgroup to an exact representation;
2. to write the support projection as a finite group average.

Both uses are replaced by the Kazhdan spectral projection
`p_n = 1_[kappa^2/2, oo)(A_n)` of `D`, where `A_n` is the Laplacian of a
Kazhdan pair of `D`.  Three facts make this work:
- the spectrum of `A_n` has an asymptotic gap;
- `p_n` asymptotically commutes with `V_n(N_G(D))`, which contains `C` and
  `L`;
- `p_n` is, up to arbitrarily small norm, a fixed finite linear
  combination of the lifts of elements of `D`.

The rank-normalized transport through the compressor is unchanged.  The
final contradiction compares two quantities:
- the corner trace of `A_n`, at least `(kappa^2/2) rank(p_n)`;
- the same trace computed from HS-commutativity, `o(rank(p_n))`.

**First instance.**  The instance is
`torsion-free-kazhdan-lamp-wreath-radical-has-kazhdan-subgroups`.
It is a torsion-free, finitely generated, sofic group whose MF radical
contains infinite Kazhdan subgroups.  The locally finite criterion and
the torsion-collapse theorem cannot reach it.

DERIVATION
kazhdan-centralizer-commuting-conjugates-proof
