---
rg: 2
id: k-amenable-compressors-need-infinite-projections
kind: claim
title: A one-sided compression certificate over an amenable subgroup has zero defect, and over a K-amenable subgroup its defect is a K0-trivial infinite projection of the subgroup's own maximal algebra
distinct_from:
  maximal-group-cstar-infinite-under-strict-compression: that shows a strict Kazhdan compression makes the maximal algebra of the AMBIENT group infinite; this shows that for any subgroup-intrinsic certificate the defect projection already lives in the maximal algebra of the SUBGROUP with vanishing regular trace, is zero when the subgroup is amenable, and has zero K0 class when the subgroup is K-amenable, so the infiniteness must already sit in the subgroup's own maximal algebra.
  a-t-menable-groups-have-no-rigid-compression-defect: that kills rigid Kazhdan pairs inside an a-T-menable group by finiteness; this kills every subgroup-intrinsic projection certificate, Kazhdan or not, over an amenable subgroup, and forces one over an a-T-menable subgroup to exhibit an infinite projection in the subgroup's maximal algebra.
  kazhdan-mapping-tori-have-proper-stably-finite-radical: that shows no stably finite certificate proves an exact extrinsic radical for Kazhdan mapping tori; this is about the one-sided order step of the compression criterion over non-Kazhdan subgroups and locates its defect in K-theory.
  property-t-free-leavitt-full-mf-radical: that is the Kazhdan-free goal; this is a method obstruction for it, which says where a compression proof without property (T) must place its subgroup.
artifacts:
  - research/k-amenable-compressors-need-infinite-projections-proof.md
  - research/artifacts/bc-gap-label-subgroup-support-2026-09-12.md
  - non_mf_groups_exist.tex
---

**ESTABLISHED.**

**Certificates.** Let `L` be a countable group and let `alpha : L -> L` be an
injective homomorphism. It induces a unital `*`-endomorphism
`alpha_* : C*_max(L) -> C*_max(L)`. A **subgroup-intrinsic one-sided
certificate** over `(L, alpha)` is a projection `p` in `C*_max(L)` with

```text
p <= alpha_*(p)          in C*_max(L).
```

Its **defect** is the projection `q = alpha_*(p) - p`.

Whenever `L <= G` and `u in G` satisfies `u l u^-1 = alpha(l)` for all `l` in
`L`, every unitary representation `sigma` of `G` in a unital C*-algebra `B`
gives `P <= U P U*`, where `P = sigma(p)` and `U = sigma(u)`. In particular
this holds in the adjoint norm corona of `thm:transport` in
`non_mf_groups_exist.tex`, and there `U P U* - P = sigma(q)`.

The Kazhdan projection is the model case: `L` has (T), `p = e_L`, and
`alpha = Ad(u)` for a compressor `u L u^-1 <= L`. Then
`e_L <= alpha_*(e_L)` holds in `C*_max(L)`, since in every representation
`alpha_*(e_L)` projects onto the vectors fixed by `alpha(L)`, and these
include the vectors fixed by `L`. That is the order of
`lem:kazhdan-projection-order`.

**Theorem.** Let `lambda_L : C*_max(L) -> C*_r(L)` be the regular
representation.

1. **(Regular invisibility.)** `lambda_L(q) = 0` for every such certificate
   and every countable `L`.
2. **(Amenable subgroups.)** If `L` is amenable, then `q = 0`. So
   `alpha_*(p) = p` in `C*_max(L)`, and therefore `U P U* = P` in every
   unitary representation of every ambient group.
3. **(K-theoretic dichotomy.)** Let `x = [q]` in `K_0(C*_max(L))`. Then:
   - `x = alpha_*[p] - [p]` and `(lambda_L)_*(x) = 0`;
   - if `(lambda_L)_* : K_0(C*_max(L)) -> K_0(C*_r(L))` is injective, then
     `x = 0`. In that case there is `k >= 0` such that `q (+) 1_k` is
     Murray--von Neumann equivalent in `M_(k+1)(C*_max(L))` to its proper
     subprojection `0 (+) 1_k`, whenever `q != 0`;
   - so if `(lambda_L)_*` is injective on `K_0` and `C*_max(L)` is stably
     finite, then `q = 0`.
4. **(a-T-menable subgroups.)** By the imports in the proof route, every
   a-T-menable `L` is K-amenable, and then `(lambda_L)_*` is an isomorphism.
   So for a-T-menable `L`, a certificate with nonzero defect exists only if
   `C*_max(L)` is not stably finite.

**Consequence for the compression criterion.**

- **Idle when the defect vanishes.** The criterion's only MF-specific step is
  "stable finiteness of the corona turns `P <= U P U*` into equality". When
  `q = 0` this equality already holds in `C*_max(G)`, and so in every unitary
  representation of `G` on every Hilbert space. The step is then idle: no
  certificate with `q = 0` can separate MF images from arbitrary unitary
  images of `G`.
- **Amenable subgroups.** Every subgroup-intrinsic certificate over an
  amenable `L` is idle, whatever `p` is.
- **Haagerup subgroups.** A non-idle certificate over an a-T-menable `L` needs
  a projection `q != 0` with `lambda_L(q) = 0`, `[q] = 0`, and
  `q (+) 1_k ~ 1_k` in `M_(k+1)(C*_max(L))`. That is an infinite projection
  in a matrix algebra over the subgroup's **own** maximal algebra.
- **Non-K-amenable subgroups.** Here `ker (lambda_L)_*` can be nonzero, so
  the defect class need not vanish. For an infinite Kazhdan `L` the kernel
  contains `[e_L] != 0`: the trivial character sends `[e_L]` to `1`, while
  `lambda_L(e_L) = 0`.

**Invariant and where each member dies.** The invariant is the class of the
defect in `ker((lambda_L)_* on K_0)`, together with the stable finiteness of
`C*_max(L)`. Every member of the class dies at the one-sided order step:

- over amenable `L`, the defect is zero before any corona is formed;
- over K-amenable `L` with stably finite `C*_max(L)`, the defect is zero as
  well, because its `K_0` class is zero and `M_(k+1)(C*_max(L))` is finite.

**For the Kazhdan-free goal.** A compression proof of
`property-t-free-leavitt-full-mf-radical` of this subgroup-intrinsic shape,
inside `Delta = St_20(L_(F_2)(1,2)) ~= R^x`, must use a subgroup `L` of one of
two kinds:

- **(K-ghost)** `L` is not K-amenable in the strong sense that
  `(lambda_L)_*` is not injective on `K_0`. This is the relative-rigidity
  regime; `jacobson-regular-character-not-mf-without-property-t` records that
  its spectral input there is equivalent to relative `(tau)`.
- **(Haagerup-infinite)** `L` is a-T-menable, and `C*_max(L)` has a
  `K_0`-trivial infinite projection in `ker lambda_L`.

For `L = V` (Thompson's group, which embeds in `R^x` and has the Haagerup
property), the second kind asks for such a projection in the maximal algebra
of `V`. Whether one exists is not decided here.

For amenable `L`, the second kind is empty.

Derivation: `k-amenable-compressors-need-infinite-projections-proof`.
