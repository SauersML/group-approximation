---
rg: 2
id: leavitt-tensor-steinberg-kernel-is-stable-k2
kind: claim
title: Over B tensor L_2 the unstable Steinberg kernel is central and equals K_2 in the stable range, so finite generation of K_2 decides the host criterion
distinct_from:
  leavitt-tensor-elementary-host-criterion: that assumes finite normal generation of one unstable kernel K_(2,n) and concludes that E_n(B tensor L) is finitely presented simple; this identifies that kernel with the stable group K_2(B tensor L), turning the hypothesis into a K-theory statement.
  simple-inputs-have-fp-elementary-leavitt-tensor-hosts: that is the open existence premise for B; this is a criterion for its kernel half, stated through K_2 and twisted Nil groups.
  leavitt-tensor-hosts-acyclic-steinberg-and-fp: that makes the kernel trivial when K_1 and K_2 vanish; this handles nonzero K_2, where the kernel is a finitely generated central subgroup exactly when K_2 is finitely generated.
artifacts:
  - research/artifacts/bh-leavitt-path-steinberg-hosts-2026-09-12.md
---

**OPEN.** Let `B` be a simple unital `F_2`-algebra, `L = L_(F_2)(1,2)` and
`R = B ⊗ L`. Then there is `n_0` (expected `n_0 = 4` or `5`) such that for
`n >= n_0`:
1. `K_(2,n)(R) := ker(St_n(R) -> E_n(R))` is central in `St_n(R)`;
2. the stabilization map `K_(2,n)(R) -> K_2(R)` is an isomorphism;
3. hence `K_(2,n)(R)` is finitely normally generated in `St_n(R)` iff `K_2(R)` is a
   finitely generated abelian group.

**Criterion consequence.** With `leavitt-tensor-elementary-host-criterion`, for
`B` finitely presented central simple and `S <= B^x` perfect, `E_n(R)` is a
finitely presented simple host of `S` as soon as `K_2(B ⊗ L)` is finitely
generated. `K_1` plays no role.

**Where `K_2(R)` sits.** Ara--Brustenga--Cortiñas Theorem 8.6 gives
`KH(A ⊗ L) = 0` for every ring `A`. So `K_2(R)` is the difference between
`K`- and `KH`-theory in degree two, a twisted Nil group of the corner-skew
Laurent structure (ABC Theorem 5.10).
- **Vanishing:** it is `0` whenever `R` is `K_2`-regular (Weibel: `K_n`-regular
  implies `K_m = KH_m` for `m <= n`), in particular when `B` is regular
  supercoherent (`ara-cortinas-leavitt-tensor-k-theory-vanishes`).
- **Expectation:** Nil groups are typically either `0` or infinitely generated, so
  in practice item 3 reduces to vanishing.

## Attempts

- **Item 1.** Khanh Lemma 5.2 states "For any unital ring B and m >= 3,
  j_m(N_m(B)) is central", quoted in
  `research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md`. The step
  still to write is that `j_m(N_m)` normally generates `K_(2,m)` in the ranks used.
- **Item 2.** Stability should follow from the frame-complex connectivity
  `H̃_d(X_r(R)) = 0` for `d <= r-3` (artifact Corollary 2.5 for `B ⊗ L`), through
  the standard spectral sequence argument for homology stability of `GL_r`
  (van der Kallen; Charney) in degree two, combined with the plus construction
  `H_2(St) -> K_2`. Not written. The rank bound depends on the connectivity
  slope, which is `r - 3` here.
- **Graph factors do not help.** For coefficient algebras `B` with
  `ABC Theorem 7.6` available (regular supercoherent), `K_*(B ⊗ L_(F_2)(E))` is
  the homotopy cofibre of `1 - N_E^t` on `K_*(B)^V`. It vanishes for every such
  `B` only if `det(1 - N_E^t) = ±1`, i.e. only for `L_2` and its Cuntz splice
  (`leavitt-path-k-theory-over-finite-fields-via-det` covers `B = F_q`). So `L_2`
  is already the best Leavitt factor, and universality has to come from `B`
  (`complexity-bounded-host-classes-are-not-universal`).
