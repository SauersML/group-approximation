---
rg: 2
id: acylindrical-hosts-break-witness-host-inner-pigeonhole
kind: claim
title: The host-inner pigeonhole dies for acylindrical hosts - the Ollivier--Wise Rips kernel is an acylindrically hyperbolic Kazhdan host, acting both properly and coboundedly, in which no power of its infinite-order automorphism is host-inner
distinct_from:
  rel-hyperbolic-hosts-make-witness-powers-host-inner: that proves host-innerness of a power of phi for every relatively hyperbolic host by Drutu--Sapir pigeonhole; this proves that the same statement, and the same pigeonhole, are false for acylindrically hyperbolic hosts, both proper and cobounded, so its 'Not claimed' extension cannot be proved from property (T) and acylindricity.
  ollivier-wise-z-torus-kernel-not-finitely-presented: that establishes the Ollivier--Wise torus over Z and its infinite outer order; this uses it as the counterexample host and adds acylindrical hyperbolicity of the kernel, its two acylindrical models, and the bounded scaling factors of the powers.
  fa-groups-finitely-many-homs-to-rel-hyperbolic-groups: that is finiteness of non-parabolic homomorphisms from FA groups into relatively hyperbolic groups; this shows finiteness of non-elliptic homomorphisms from Kazhdan groups into acylindrically hyperbolic groups fails, already for a single image.
  finite-outer-order-radical-witnesses-cross-alekseev-thom: that splits witnesses by the outer order of phi; this shows acylindrical hyperbolicity of a Kazhdan kernel does not force the finite-order side.
artifacts:
  - research/acylindrical-hosts-break-witness-host-inner-pigeonhole-proof.md
  - research/osin-acylindrical-trichotomy-and-cayley-models.md
  - research/ollivier-wise-z-torus-kernel-not-finitely-presented.md
  - research/rel-hyperbolic-hosts-make-witness-powers-host-inner.md
---

**ESTABLISHED** through `acylindrical-hosts-break-witness-host-inner-pigeonhole-proof`.

Let `1 → N → G_OW → Z → 1` be the Ollivier--Wise torus over `Z`
(`ollivier-wise-z-torus-kernel-not-finitely-presented`): `G_OW = N ⋊_φ <t>` is finitely presented,
torsion-free and word-hyperbolic with `cd ≤ 2`; `N` is Kazhdan, torsion-free and not finitely
presented; and `[φ]` has infinite order in `Out(N)`. Fix a finite generating set `S` of `G_OW`.

## Theorem

1. **(Two acylindrical models.)** `N` is acylindrically hyperbolic. It acts acylindrically, with
   unbounded orbits, on two hyperbolic graphs:
   - `Y_prop = Cay(G_OW, S)`, restricted to `N`. This action is **proper** (free on vertices, with
     a locally finite graph) and **not cobounded**.
   - `Y_cob = Γ(N, X)`, for a generating set `X` given by Osin (AH1). This action is **cobounded**
     (vertex-transitive) and non-elementary.
2. **(No host-inner power.)** Take the host `H = N`, with either action, and `ψ = id_N`. Then
   `ψ(N) = N` is not elliptic. But there are **no** `m ≥ 1` and `h ∈ H` with
   `ψ ∘ φ^m = c_h ∘ ψ`. Equivalently, the homomorphisms `ψ ∘ φ^n : N → H` (`n ≥ 0`) all have the
   same image and are pairwise non-conjugate in `H`. So a Kazhdan group can have infinitely many
   conjugacy classes of non-elliptic homomorphisms into an acylindrically hyperbolic group, all with
   the same image.
3. **(Non-divergence is not enough.)** On `Y_prop`, the Groves--Hull scaling factors of these maps
   are uniformly bounded: `‖ψ φ^n‖ ≤ max_{s ∈ S_N} |s|_S` for every `n`, where `S_N` is a finite
   generating set of `N`. The quasi-centres `t^n` drift to infinity in `N \ Y_prop`. So the sequence
   `(ψ φ^n)` is non-divergent in the sense of Groves--Hull Definition 4.2, and still meets
   infinitely many conjugacy classes.
4. **(Kernel form.)** "An acylindrically hyperbolic Kazhdan group with a finitely presented
   (even hyperbolic, two-dimensional) mapping torus has finite outer order" is false. So the
   analogue for acylindrical kernels of Corollary 1 of `rel-hyperbolic-hosts-make-witness-powers-host-inner`
   fails as a statement about Kazhdan groups.

## What this kills (class kill)

- **The class.** Arguments that extend the host-inner theorem to acylindrical hosts, i.e. that
  prove (HI) `ψφ^m = c_h ψ` for some `m ≥ 1`, and hence "`H` not MF" by Cases A/B, from the
  following inputs only:
  - `K` finitely generated, torsion-free, Kazhdan (so FA and every consequence of FR);
  - `φ ∈ Aut(K)` of infinite outer order, with `K ⋊_φ Z` finitely presented, even hyperbolic of
    `cd ≤ 2`, and `K` infinitely presented;
  - `H` acting acylindrically on a hyperbolic space with `ψ(K)` non-elliptic, where the action may
    be taken **proper**, or **cobounded**, or `H` may be taken acylindrically hyperbolic,
    torsion-free and Kazhdan.
- **Named invariant.** The class of `[φ]` in `Out_H(ψK) = N_H(ψK) / ψ(K) C_H(ψK)`. For `H = N`
  it is `[φ] ∈ Out(N)`, which has infinite order.
- **Where every member dies.** Step 1 of `rel-hyperbolic-hosts-make-witness-powers-host-inner-proof`:
  "the `ψφ^n` fall into finitely many `H`-conjugacy classes". The two ways an acylindrical action
  can fail to give finiteness both occur here:
  - on `Y_prop`, bounded displacement is available, but the quasi-centres escape every compact
    set of `N \ Y`;
  - on `Y_cob`, the quasi-centres can be brought back by `H`, but a bounded-displacement set is not
    finite: acylindricity bounds only elements that almost fix two far-apart points.
  The Drutu--Sapir hypothesis supplies exactly this missing finiteness. A proper cobounded action
  on a hyperbolic geodesic space makes the host hyperbolic (Švarc--Milnor), where Drutu--Sapir
  applies. Dropping either properness or coboundedness already breaks the step.
- **Consequence for the flagship.** For a witness `(G, K)` of `torsion-free-sofic-exact-mf-radical-over-z`
  in region (IO), an acylindrically hyperbolic kernel is not excluded by any argument of this class.
  Any proof that (IO), or (IO-ext), contains no acylindrically hyperbolic kernel must use one of
  the witness-only inputs listed in `ollivier-wise-z-torus-kernel-not-finitely-presented`:
  - (S) soficity;
  - (Q) quotientlessness of `K`;
  - (R) `K ⊆ Rad_MF(G)`.
  None of these is known for the Ollivier--Wise torus, and none is contradicted by it.

## Not claimed

- The conclusion-level statement "every acylindrical host of a witness kernel is non-MF" is
  **not refuted**. The host `N` here is not known to be MF or non-MF, and `N` is not known to be a
  witness kernel. What is refuted is the host-inner step (HI), and with it the w17 route to that
  conclusion.
- No finitely presented counterexample host is given. Every host built here is `N` itself, which
  is finitely generated but infinitely presented.
- Nothing about Groves--Hull beyond Definition 4.2 is used. It is quoted in the proof for context
  only, and is not load-bearing.
