---
rg: 2
id: kt-double-shortest-fold-repair-is-a-bare-wall
kind: claim
title: Repairing the shortest Kun--Thom double fold already produces a bare relative wall
distinct_from:
  kt-double-canonical-vertex-marginals-admit-large-amalgam-twists: That constructs exact residual vertex pairs which move an actor visible outside the finite image of the amalgam; this identifies the compressor return lying in every finite amalgam image, proves exact collapse there, and quantifies the density cost of repairing it.
  kt-double-hyperlinear-iff-mixed-word-trace-selection: That requires all mixed reduced-word traces and is equivalent to hyperlinearity of the whole double; this proves that repairing one particular length-two trace already gives the weaker bare-wall detector sufficient for the radical-collision route.
  bare-relative-wall-exists: That is the open existence assertion for one wall in an arbitrary Connes-embeddable model; this is a conditional extraction theorem saying any bounded-block repair of the shortest double fold contains such a wall.
---

Fix a strict Kun--Thom compressor

```text
t Gamma t^(-1)<Gamma,
```

choose `gamma in Gamma\t Gamma t^(-1)`, and put

```text
h=t^(-1) gamma t notin Gamma,
w_h=i_0(h)i_1(h)^(-1) in D=G *_Gamma G.                (KFR1)
```

Then `w_h` is the shortest possible mixed reduced word: it is reduced of
amalgam length two, while a word of length one lies in a single vertex.

The following four statements hold.

1. **Every exact finite-dimensional vertex pair folds.**  If
   `rho_0,rho_1:G->U(d)` are genuine representations with
   `rho_0|Gamma=rho_1|Gamma`, then

   ```text
   rho_0(h)=rho_1(h),
   ```

   so the induced representation of `D` sends `w_h` to `1`.  In particular
   every residual coset-sign/commutant twist has this defect, independently
   of the chosen signs.

2. **A direct-sum repair has macroscopic density.**  Suppose a pair of
   asymptotic vertex maps is a direct sum of one exact sector and at most
   `R` repair sectors,

   ```text
   rho_(epsilon,n)=rho_(epsilon,n)^ex
          direct_sum (direct_sum_(r=1)^R eta_(epsilon,n)^r),          (KFR2)
   ```

   where the exact pair agrees on `Gamma`.  If

   ```text
   tr(rho_(0,n)(h)rho_(1,n)(h)^*) -> 0,                 (KFR3)
   ```

   then the total repair density is at least `1/2-o(1)`.  After passing to a
   subsequence, one fixed repair sector has density at least `1/(2R)-o(1)`,
   its vertex multiplicativity and `Gamma`-agreement defects tend to zero,
   and

   ```text
   liminf ||eta_(0,n)^r(h)-eta_(1,n)^r(h)||_2^2 >= 2/R. (KFR4)
   ```

3. **One repaired sector is already a wall.**  In the tracial matrix
   ultraproduct put

   ```text
   pi(g)=diag(eta_0^r(g),eta_1^r(g)),
   S=[[0,1],[1,0]].                                      (KFR5)
   ```

   The vanishing defects make `pi` a homomorphism, `Gamma`-agreement gives
   `S in pi(Gamma)'`, and `(KFR4)` gives `[S,pi(h)]!=1`.  Thus `(pi,S)` is a
   bare relative wall.  By `bare-wall-radical-collision-route`, the existence
   of the bounded-block repair already produces a hyperlinear nonsofic
   group; it is not a weaker intermediate construction.

4. **Canonical vertex marginals are free once the repair exists.**  Tensor
   both repaired vertex maps with the same residual finite-quotient regular
   representation `sigma_n` of `G`.  Then

   ```text
   eta_hat_(epsilon,n)(g)=eta_(epsilon,n)^r(g) tensor sigma_n(g)       (KFR6)
   ```

   has canonical vertex character, preserves every vertex and
   `Gamma`-agreement defect, and preserves the fold exactly because the
   common tensor factor cancels:

   ```text
   eta_hat_0(h)eta_hat_1(h)^*
      =(eta_0^r(h)eta_1^r(h)^*) tensor 1.                (KFR7)
   ```

Consequently a vanishing-density correction cannot repair even the shortest
mixed trace.  A bounded number of positive-density corrections can do so
only by containing one genuinely non-exact full-actor block which already
solves the bare-wall instance of Pestov Question 3.4.
