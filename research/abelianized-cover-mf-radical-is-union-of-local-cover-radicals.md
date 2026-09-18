---
rg: 2
id: abelianized-cover-mf-radical-is-union-of-local-cover-radicals
kind: claim
title: The MF radical and the LEF kernel of the abelianized cover are unions of images from finitely presented local-commutator covers
distinct_from:
  full-mf-radical-has-fp-cover-same-generators: that gives a finitely presented cover of the base G with full MF radical; this writes the radical of the non-finitely-presented cover E as an increasing union of images of radicals of finitely presented groups Gamma_L lying between F and E, and says nothing about full radicals.
  full-mf-radical-groups-form-an-extension-colimit-class: that closes the zero class (full radical) under colimits; this computes an arbitrary, typically proper, MF radical of a directed quotient limit.
  abelianized-cover-df-forces-cofinite-congruence-df: that approximates E from above by its quotients H_N; this approximates E from below by finitely presented groups Gamma_L that surject onto it.
  full-mf-radical-abelianized-cover-is-not-mf: that is the open analytic statement (DF); this proves an equivalent finitary form of it, not DF itself.
artifacts:
  - research/abelianized-cover-mf-radical-local-cover-proof.md
---

**ESTABLISHED** (complete proof in the route file).

**General continuity.**  Let `F` be a free group on a finite set `X`, and
let `K_1 <= K_2 <= ...` be normal subgroups with `K = U_L K_L`.  Put
`H = F/K`, `H_L = F/K_L` and `pi_L : H_L -> H`.  Then

```text
Rad_MF(H) = U_L pi_L( Rad_MF(H_L) ),                                (U1)
```

and the union is increasing.  If each `K_L` is the normal closure of a
finite set, then also

```text
H is LEF   <=>   U_L pi_L( fr(H_L) ) = 1,                            (U2)
```

where `fr` is the finite residual, the intersection of all finite-index
normal subgroups.  An amplification step is used along the way: if
`g notin Rad_MF(Gamma)`, then some corona homomorphism `sigma` has
`||sigma(g) - 1|| >= sqrt 3`.

**The abelianized cover.**  Let `G = <X | r_1, ..., r_m>` be finitely presented
with `F = F(X)` and `R = <<r_j>>`, and let `c = max |r_j|`.  Put

```text
N_L     = << [u,v] : u, v in R, |u|, |v| <= L >>,
Gamma_L = F / N_L.
```

Then `N_L` is finitely normally generated, `U_L N_L = [R,R]`, and each
`Gamma_L` is a finitely presented group that surjects onto `E = F/[R,R]`.

1. **DF is finitary.**  `E` is non-MF, i.e. `(DF)` holds for this
   presentation, iff there are an `L` and a word `w in [F,F] \ [R,R]` with
   `w N_L in Rad_MF(Gamma_L)`.  If this holds at `L`, it holds at every
   `L' >= L`.
2. **The exact-permutation class is finitary.**  `E` is LEF iff no word
   `w notin [R,R]` lies in the finite residual of any `Gamma_L`.  LEF implies
   MF, so `(DF)` forces some `Gamma_L` to be non-residually-finite on a word
   that survives in `E`.  Since `Rad_MF <= fr` for finitely generated groups,
   this is also implied by item 1.
3. **Shape of the witnesses.**  `Gamma_L^ab = Z^|X|`.  Hence
   `Rad_MF(Gamma_L)` and `fr(Gamma_L)` lie in `[Gamma_L, Gamma_L]`, and
   `Gamma_L` is not Kazhdan.  If `G` has no nontrivial finite quotient, then
   every finite quotient `phi : Gamma_L ->> P` satisfies:
   - `P = phi(R)` and `[P,P] = phi([R,R])`;
   - if `P` is non-abelian, then `diam_X(P) >= (L - c + 1)/2`.

   Abelian finite quotients factor through `Z^|X|`, so they detect no word of
   `[F,F]`.
4. **Threshold.**  Let `L* = min{ L : pi_L(Rad_MF(Gamma_L)) != 1 }`, in
   `[1, infinity]`.  `(DF)` holds iff `L* < infinity`.  If `L` is below the
   length of the shortest nontrivial element of `R`, then `Gamma_L = F` is
   MF, so `L*` is at least that length.
   - Consequently, `(DF)` for `E` is the same as `(DF_L)`, that
     `pi_L(Rad_MF(Gamma_L)) != 1`, for one finite `L`.
   - A certificate of `(DF_L)` involves only the finitely many relations
     `[u,v] = 1` with `u, v in R cap S_L`.
   - The lamp calibration `relation-lamp-wreath-is-mf-with-nontrivial-fd-radical`
     says only that a proof must use some of these relations.
