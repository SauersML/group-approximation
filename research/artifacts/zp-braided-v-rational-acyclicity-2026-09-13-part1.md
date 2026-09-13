# bV is rationally acyclic: part 1, overview and the homology of the kernel

Lane z2-09-bv-acyclic, 2026-09-13. Unreviewed. Parts 2 and 3 complete the proof.

**Theorem.** For the Brin–Dehornoy braided Thompson group `bV`, `H_n(bV; Q) = 0`
for every `n ≥ 1`.

**Plan.**

- `K = ker(bV → V)` is the colimit of pure braid groups under cabling.
- Step A (this part): `H_q(K; Q)` is a finite sum of configuration modules
  `C_c(Conf_m(C), Q) ⊗_{Q[Σ_m]} W`.
- Step B (part 2): `C(C^j, Q)` is V-acyclic, from Palmer–Wu's acyclicity of the
  labelled Thompson groups `V(Q^j)`.
- Step C (part 3): configuration modules are V-acyclic, by stratifying `C^m`.
- Step D (part 3): the Lyndon–Hochschild–Serre spectral sequence with `V`
  acyclic (Szymik–Wahl).

**External inputs.**

- Szymik–Wahl, arXiv:1411.5035: `V` is acyclic.
- Palmer–Wu, arXiv:2510.16879, Theorem 2.6: `V(G)` is acyclic for every discrete `G`.
- F. Cohen, "The homology of C_{n+1}-spaces", LNM 533 (1976), in the exposition of
  D. Sinha, arXiv:math/0610236, Theorem 6.3: the homology of the little disks
  operad is the graded Poisson (for `R^2`, Gerstenhaber) operad.

## Step A: `H_q(K; Q)` as a `V`-module

**A1 (kernel and action).** As in `braided-thompson-group-bv-is-perfect-proof`
(Step 1), `K = colim_T P_{L(T)}` over binary trees `T` ordered by expansion,
with cabling maps as transition maps. `P_n` is the fundamental group of the
aspherical space `Conf_n(R^2)`.

For `g = (T_-, γ, T_+) ∈ bV`, conjugation sends `(T_+, β, T_+)` to
`(T_-, γβγ^{-1}, T_-)`. On `H_*(P_n) = H_*(Conf_n(R^2))`, conjugation by
`γ ∈ B_n` is the deck transformation relabelling points by the permutation of
`γ`. Braids with the same permutation differ by pure braids, which act
trivially on homology. So `bV` acts on `H_*(K)` through `V`, by relabelling
leaves.

**A2 (Cohen).** `H_*(Conf_n(R^2); Z)` is torsion-free. As a `Σ_n`-module with
operad compositions it is the Gerstenhaber operad `e_2(n)`: a basis is given
by products, over the blocks `B` of a partition `π` of `[n]`, of iterated
brackets of the letters in `B`. A block contributes degree `|B| − 1` and a
singleton contributes the degree-0 letter. The degree is `n − #π`.

**A3 (cabling).** Cabling strand `i` replaces it by two parallel strands. On
configuration spaces this inserts two nearby points at `x_i`, which is operadic
composition `∘_i` with the degree-0 class `μ = x_{i'} x_{i''}` of `Conf_2(R^2)`.
In `e_2` the bracket is a derivation of the degree-0 product, with no signs
since `μ` has degree 0. So on basis elements:

- if `i` is a singleton, the image has `i` replaced by two singletons `i'`, `i''`;
- if `i` lies in a block `B` with Lie word `w`, the image is
  `w[i → i'] · x_{i''} + x_{i'} · w[i → i'']`.

**A4 (support).** The support `S` of a basis element is the union of its
blocks of size `≥ 2`. Then `H_q(Conf_n) = ⊕_S H_q(Conf_n)_S`, and `Σ_n`
permutes supports. `H_q(Conf_n)_S ≅ W_{S,q}`, the span of bracket-product data on
partitions of `S` into blocks of size `≥ 2` with `|S| − #blocks = q`. So
`m = |S|` satisfies `q + 1 ≤ m ≤ 2q`, and `W_{m,q}` is a finite-rank free
`Z`-module with a `Σ_m`-action. By A3, cabling at `i ∉ S` fixes the `S`-summand
data. Cabling at `i ∈ S` sends it to the sum of the same data on `S[i → i']`
and on `S[i → i'']`.

**A5 (colimit).** Homology commutes with filtered colimits, so
`H_q(K; Q) = colim_T H_q(Conf_{L(T)}; Q)`. By A4 this is
`⊕_m colim_T ( Q[Inj([m], L(T))] ⊗_{Q[Σ_m]} W_{m,q} )`, where refinement of a
leaf acts on injections additively: an injection hitting the leaf goes to the
sum of the two injections hitting its children.

An injection `[m] → L(T)` is an ordered `m`-tuple of pairwise disjoint dyadic
cones, i.e. a box `U_1 × ... × U_m ⊆ Conf_m(C)`. Sending a box to its indicator
identifies the additive colimit with `C_c(Conf_m(C), Q)`:

- it is compatible with refinement;
- the boxes at one level are disjoint, so their indicators are independent;
- every compact open subset of `Conf_m(C)` is a finite disjoint union of boxes
  at a common level.

By A1, `V` acts through its action on `C`, commuting with `Σ_m`. Hence, for
every `q ≥ 1`, as `V`-modules:

`H_q(K; Q) ≅ ⊕_{m=q+1}^{2q} C_c(Conf_m(C), Q) ⊗_{Q[Σ_m]} W_{m,q}`.

**Check (q = 1).** `m = 2` and `W_{2,1} = Q` with trivial `Σ_2`-action, because
the Gerstenhaber bracket of two degree-0 letters is symmetric. This gives
`C_c` of unordered pairs of distinct points, matching `H_1(K) ≅ C_c(Y, Z)` in
`braided-thompson-group-bv-is-perfect-proof`.
