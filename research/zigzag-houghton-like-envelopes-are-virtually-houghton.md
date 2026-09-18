---
rg: 2
id: zigzag-houghton-like-envelopes-are-virtually-houghton
kind: claim
title: For the zigzag enumeration of Z, every Houghton-like envelope H_n(E_nu(Z)) is commensurable with the Houghton group H_(4n), hence of type F_(4n-1) and not FP_(4n)
requires:
  - zigzag-cyclic-shift-envelope-is-finitely-presented
  - houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group
  - houghton-like-groups-are-strongly-shift-similar
distinct_from:
  zigzag-cyclic-shift-envelope-is-finitely-presented: that is the case n = 1 (E_nu(Z) has index 12 in E_4, type F_3, not FP_4); this is every n >= 1, by transporting finite index through the Houghton-like construction.
  free-shift-houghton-like-envelopes-are-not-fp: that kills free-shift (generic) enumerations for every n; this is the positive rigid case the refutation leaves open, and it shows the rigid case is attained.
  houghton-like-envelopes-lift-finite-presentation-from-germs: that lifting claim is refuted in general; this is an instance where the conclusion holds because the envelope is eventually periodic.
---

**ESTABLISHED** (lane proof, elementary, written inline; not independently reviewed; no priority claimed — for
`E_k` itself the finite-index observation is Mallery–Zaremsky's remark after their Question 5.13).

**Statement.** Let `nu : Z -> N` be the zigzag enumeration of `zigzag-cyclic-shift-envelope-is-finitely-presented`
and `G = E_nu(Z)`. For every `n >= 1`, `H_n(G)` has finite index in `H_n(E_4)`, which contains `H_n(H_4) ≅ H_(4n)`
with finite index. So `H_n(G)` is commensurable with the Houghton group `H_(4n)`. By Brown, it is of type
`F_(4n-1)` and not of type `FP_(4n)`; in particular it is finitely presented for every `n >= 1`.

**Lemma (finite index passes through H_n).** Let `FSym(N) <= G <= G' <= Sym(N)` with both strongly shift-similar
and `[G' : G] < ∞`. Then `H_n(G)` has finite index in `H_n(G')` for every `n >= 1`.

*Proof.* `Germs(G)` has finite index in `Germs(G')`. With the common near shift `s̄`, `Ĝ = Germs(G) ⋊ <s̄>` has
finite index in `Ĝ'`, so `Ĝ^n` has finite index in `Ĝ'^n`. Hence `Q_n(Ĝ) = Q_n(Ĝ') ∩ Ĝ^n` has finite index in
`Q_n(Ĝ')` (notation of `houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group`). That node's item 1 identifies
`H_n(G)/FSym([n] x N)` with `Q_n(Ĝ)` through ray germs, and `H_n(G)` contains `FSym([n] x N)`
(`houghton-like-groups-are-strongly-shift-similar`). So `H_n(G)` is the full preimage of `Q_n(Ĝ)` under the germ
map of `H_n(G')`, and the index is preserved. ∎

**Proof of the statement.**
- `G` has index 12 in `E_4` and contains `E_2 ⊇ FSym(N)` (`zigzag-cyclic-shift-envelope-is-finitely-presented`);
  both are strongly shift-similar. The lemma gives `[H_n(E_4) : H_n(G)] < ∞`.
- `E_4 ≅ S_4 ⋉ H_4` (Mallery–Zaremsky, lemma on eventually periodic permutations, read in the source TeX), so `H_4`
  has index 24 in `E_4` and contains `FSym(N)`. The lemma gives `[H_n(E_4) : H_n(H_4)] < ∞`, and
  `H_n(H_4) ≅ H_(4n)` (Mallery–Zaremsky, Proposition 5.5, imported in
  `houghton-like-groups-are-strongly-shift-similar`).
- `H_m` is of type `F_(m-1)` and not `FP_m` (Brown 1987, as recalled in Mallery–Zaremsky §5; not re-read at
  source). These properties pass to finite-index subgroups and overgroups. ∎

**Reading for the Houghton-like route (`decidable-inputs-have-fp-houghton-like-shift-envelopes`).**
- The rigid alternative left by `free-shift-houghton-like-envelopes-are-not-fp` is realized for `P = Z`. It adds
  nothing new for Boone–Higman, since `E_nu(Z)` was already finitely presented.
- The mechanism here is eventual periodicity, and `finite-ray-shift-envelopes-require-virtually-cyclic-input`
  confines it to virtually cyclic inputs. A non-virtually-cyclic input needs an enumeration that is rigid in the
  sense of `fsym-containing-fp-groups-are-pinned-by-finitely-many-equations`: every far transplant of
  `rho`-edges must create a Schreier ball that does not already occur. Eventually periodic `rho` is rigid because
  `rho`-edges stay a bounded structural distance from their source. The natural next candidates are unbounded
  but locally linear patterns, where near relations such as `lambda s lambda^-1 = s^k` make every local
  transplant detectable.
