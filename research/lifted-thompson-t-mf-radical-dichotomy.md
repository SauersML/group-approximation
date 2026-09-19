---
rg: 2
id: lifted-thompson-t-mf-radical-dichotomy
kind: claim
title: "The MF radical of the lifted Thompson group T-bar is either trivial or everything; if it is everything, then T, every rotation centralizer C_T(r_k), and V all have full MF radical"
distinct_from:
  deligne-triple-cover-mf-radical-dichotomy: that shows the radical of Deligne's triple cover is trivial or the central kernel C_3, so there the central branch is the non-MF branch; here the dilation endomorphism of T-bar rules out every central branch, and the only non-MF branch is the full radical.
  lifted-thompson-t-quotients-are-rotation-centralizers: that identifies T-bar/<z^(2^k)> with C_T(r_k) as abstract groups; this spends that identification, with subgroup heredity of MF, to compare MF radicals of T-bar and T.
  lifted-thompson-t-perfect-centre-cubically-elliptic: that proves T-bar perfect and without finite-index subgroups; this uses perfectness only to turn a radical with full image in T into all of T-bar.
---

**ESTABLISHED (written proof; not Lean-verified).**  Let `T̄` be the lift of
Thompson's group `T` to `R`: the group of homeomorphisms of `R` commuting with
`z(x) = x+1` that are piecewise linear with finitely many breakpoints mod 1,
all in `Z[1/2]`, with slopes in `2^Z`, mapping `Z[1/2]` onto itself.  Let
`p : T̄ -> T` be the projection, `ker p = <z>`, and let `r_k` be the rotation
by `2^(-k)`.  `Rad` means `Rad_MF`, the intersection of the kernels of all
homomorphisms to unitary groups of norm matrix coronas.

1. **(Dichotomy.)**  `Rad(T̄) in {1, T̄}`.  In particular no nontrivial
   subgroup `<z^m>` of the centre is ever the MF radical.
2. **(One-word criterion.)**  The following are equivalent:
   - `T̄` is not MF;
   - `z in Rad(T̄)`;
   - `Rad(T̄)` contains some nontrivial element;
   - `Rad(T̄) = T̄`, that is, every homomorphism from `T̄` to the unitary
     group of a norm matrix corona is trivial.
3. **(Downward transfer.)**  If `T̄` is not MF, then
   - `Rad(T) = T`, so Thompson's `T` is not MF;
   - `Rad(C_T(r_k)) = C_T(r_k)` for every `k >= 0`;
   - `Rad(V) = V`, so Thompson's `V` is not MF.

   Equivalently, if `T` is MF then `T̄` is MF.  More sharply, if
   `C_T(r_k)` is MF for **one** `k >= 0`, then `T̄` is MF.  The case `k = 0`
   is `T` itself.
4. **(Seed shape.)**  `T̄` is finitely presented and torsion-free.  So if `T̄`
   is not MF, it is a torsion-free finitely presented group with **full** MF
   radical, and its proof uses no Property `(T)` input.

Proof route: `lifted-thompson-t-mf-radical-dichotomy-proof`.

## What this changes

- The obvious worry about a central-extension seed is that the radical
  might be a proper central subgroup, as it is on the non-MF branch for
  Deligne's cover.  Item 1 removes that worry for `T̄`.  The engine is the
  dilation `lambda(g)(x) = g(2x)/2`, an injective endomorphism with
  `lambda(z) = t_1`, the translation by `1/2`, so `lambda(z)^2 = z`.  A
  radical `<z^m>` would be carried into itself by `lambda`, but `t_1^m`
  lies in `<z^m> = <t_1^(2m)>` only when `m = 0`.
- By item 2 the torsion-free seed `property-t-free-torsion-free-fp-non-mf-seed`
  follows from **one word**: every corona representation of `T̄` kills the
  central translation `z`.  That is the hole `lifted-thompson-t-is-not-mf`.
- By item 3 the same word also proves that `V` is not MF.  So one hole feeds
  both deep inputs of `property-t-free-manuscript-results`: the Leavitt
  endpoint, through the Thompson-`V` route recorded on the live bus in wave
  15, and the torsion-free endpoint, through the seed.
- The price is also recorded by item 3.  The hole is at least as strong as
  "`T` is not MF", and as "`C_T(r_k)` is not MF for every `k`".  An MF
  model of a single rotation centralizer refutes it.
