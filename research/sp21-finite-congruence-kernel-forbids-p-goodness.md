---
rg: 2
id: sp21-finite-congruence-kernel-forbids-p-goodness
kind: claim
title: A finite congruence kernel makes every finite-index subgroup of a cocompact arithmetic Sp(2,1) lattice fail p-goodness in degree 9, for every prime p
distinct_from:
  sp21-lattice-has-congruence-subgroup-property: that is the open assertion that the congruence kernel is finite; this is the established implication from a finite kernel to nonzero profinite mod-p cohomology in degree 9, which the discrete group cannot carry
  every-hyperbolic-group-is-good: that is the open universal goodness assertion; this proves that a lattice with the congruence subgroup property, if one exists, is a residually finite hyperbolic group that is not good
  good-groups-have-no-persistent-finite-cohomology: that is a discrete-side consequence of goodness, killing classes in finite covers; this is a profinite-side excess above the virtual cohomological dimension, forced by a finite congruence kernel
  sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel: that is the equivalence of finite rank with a finite pro-p congruence kernel; this extracts a nonzero degree-9 mod-p class of the pro-p completion from a finite pro-p kernel
  hs-stable-hyperlinear-kazhdan-hyperbolic-forces-persistent-class: that obtains non-goodness from a persistent degree-two class produced by stability; this obtains it from profinite cohomological dimension in degree 9, with no stability input
artifacts:
  - research/artifacts/sp21-congruence-goodness-2026-09-16.md
---

**ESTABLISHED.** Use the setting of
`sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel` with `G(k_{v_0}) ≅ Sp(2,1)`:
- `k` is a number field and `G` is simply connected, absolutely almost simple and
  `k`-anisotropic, compact at the other archimedean places;
- `Γ <= G(O)` is torsion-free of finite index;
- `Γ^ ->> Γ̄ <= ∏_𝔭 G(O_𝔭)` is the natural map, with kernel `C`;
- `D = 21·[k:Q]`;
- for a prime `p`, `Γ(p) = Γ ∩ G(O, pO)`, and for finite-index `Δ <= Γ(p)`, `Δ̄_p` is
  the closure of `Δ` in `∏_{𝔭 | p} G(O_𝔭)`.

1. **Full kernel.** Suppose `C` is finite. Let `p` be any prime and `Γ_1 <= Γ` any
   finite-index subgroup. Then `cd_p(Γ_1^) >= D`. There is a finite simple `Γ_1^`-module
   `A` with `pA = 0` such that
   `H^9(Γ_1^;A) != 0 = H^9(Γ_1;A)`. So `Γ_1` is neither good nor p-good.
2. **Trivial coefficients.** Suppose `C` is finite and `p` is prime. Then some
   finite-index `Γ_1 <= Γ` has `H^9(Γ_1^;F_p) != 0 = H^9(Γ_1;F_p)`.
3. **Pro-p form.** Let `p` be prime and `Δ <= Γ(p)` of finite index. Suppose the pro-p
   congruence kernel `N_Δ = ker(Δ^_p ->> Δ̄_p)` is finite. Then `cd_p(Δ^_p) >= D`, and
   `H^9(Δ^_p;F_p) != 0 = H^9(Δ;F_p)`.

The proof uses the following facts (full proof in the artifact):
- `Γ_1` is the fundamental group of a closed aspherical 8-manifold, `Γ_1\H^2_H`.
- Strong approximation makes `Γ̄_1` open.
- A finite kernel splits off on an open subgroup `M`, so `M` is isomorphic to an open
  subgroup of `G(O^)`.
- That open subgroup contains a uniform subgroup of `∏_{𝔭 | p} G(O_𝔭)` of dimension `D`.
  Lazard gives it `cd_p = D`, and closed subgroups do not raise `cd_p`.
- Serre's simple-module test turns `cd_p > 8` into a nonzero class in degree 9.
- For item 2, a closed subgroup's cohomology is the direct limit over the open subgroups
  containing it.

**Reading.**
- If `sp21-lattice-has-congruence-subgroup-property` holds, its lattice is a residually
  finite, torsion-free, Kazhdan, word-hyperbolic group that is not good.
- Conversely, goodness of one torsion-free arithmetic `Sp(2,1)` lattice refutes the
  congruence subgroup property for its `G`. So does goodness of any finite-index subgroup
  of one, or merely `cd_p(Γ_1^) <= 8` for one prime and one `Γ_1`.
- The graph already had the universal version, through universal residual finiteness.
  The lattice-local form is what is new here.
- By `sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel`, item 3 says that
  `H^9(Δ^_p;F_p) = 0` would force `rank(Δ^_p) = ∞`.
- None of these tests is a finite certificate. The degree-9 profinite cohomology is a
  direct limit over all finite quotients.
- The same proof gives degree `4n+1` for `Sp(n,1)` and degree `17` for `F_4^(-20)`
  (artifact §5).

**Novelty and trust surface.**
- **Novelty.** None claimed. This is the folklore mechanism by which the congruence
  subgroup property makes `SL_n(Z)`, `n >= 3`, not good. The Grunewald–Jaikin-Zapirain–
  Zalesskii paper exists as cited (Duke Math. J. 144 (2008), no. 1, 53–72,
  DOI 10.1215/00127094-2008-031; Crossref and Project Euclid, checked 2026-09-16), but its
  abstract does not mention `SL_n(Z)`, so the attribution of the remark is unverified.
- **Imports, not re-read in this session.**
  - Cartan: `X ≅ R^8`.
  - Strong approximation: Platonov–Rapinchuk Theorem 7.12.
  - Open uniform subgroups: Dixon–du Sautoy–Mann–Segal Corollary 8.34.
  - Lazard's theorem `cd_p = dim` for torsion-free compact p-adic analytic groups.
  - Serre, *Galois Cohomology*, I §2.2 Proposition 8, §3.1 Proposition 11, §3.3
    Proposition 14 and §4.1 Proposition 21. The numbering is from memory.
