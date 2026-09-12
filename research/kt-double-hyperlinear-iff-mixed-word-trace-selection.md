---
rg: 2
id: kt-double-hyperlinear-iff-mixed-word-trace-selection
kind: claim
title: The Kun--Thom double is hyperlinear exactly when its two vertex models have canonical mixed reduced-word traces
distinct_from:
  reduced-amalgam-canonical-trace-is-mf: That asks for the stronger operator-norm MF approximation of the canonical trace; this is the exact normalized-Hilbert--Schmidt criterion and makes no operator-norm assertion.
  kt-double-canonical-vertex-marginals-admit-large-amalgam-twists: That proves canonical exact vertex marginals and exact amalgam agreement alone do not control the double; this identifies the missing datum as the traces of genuinely mixed reduced alternating words.
  hnn-hyperlinearity-is-amalgamated-free-haar-unitary: That is the stable-letter and relative-commutant criterion for a central HNN extension; this is the two-vertex normal-form criterion for the Kun--Thom symmetric double.
---

Fix the explicit Kun--Thom Theorem E pair `Gamma<G`, put

```text
D=G *_Gamma G,
```

and write `i_0,i_1:G->D` for the two vertex embeddings.  The following are
equivalent.

1. `D` is hyperlinear.
2. There are dimensions `d_n` and maps

   ```text
   rho_(epsilon,n):G->U(d_n),             epsilon in {0,1},
   ```

   satisfying all four pointwise conditions below:

   ```text
   ||rho_(epsilon,n)(gh)
       -rho_(epsilon,n)(g)rho_(epsilon,n)(h)||_2 -> 0;       (KMW1)

   ||rho_(0,n)(gamma)-rho_(1,n)(gamma)||_2 -> 0;             (KMW2)

   tr_(d_n)(rho_(epsilon,n)(g)) -> delta_(g,1);              (KMW3)

   tr_(d_n)(prod_(j=1)^m rho_(epsilon_j,n)(g_j)) -> 0        (KMW4)
   ```

   for `g,h in G`, `gamma in Gamma`, and every reduced alternating normal
   form of length `m>=2`, meaning `g_j in G\Gamma` and
   `epsilon_j!=epsilon_(j+1)`.

Condition `(KMW4)` is the irreducible extra datum.  The established exact
models of `kt-double-canonical-vertex-marginals-admit-large-amalgam-twists`
satisfy exact vertex multiplicativity, exact agreement on `Gamma`, and
canonical vertex characters while allowing a fixed actor to remain at
normalized-Hilbert--Schmidt distance at least `sqrt(2)` between the two
copies.  Thus `(KMW1)--(KMW3)` do not imply `(KMW4)`.

This equivalence packages the fixed candidate; it does **not** reduce Pestov
Question 3.4.  By `kt-pair-group-double-is-nonsofic`, proving the existence
of the models in clause 2 already proves that this explicit nonsofic group is
hyperlinear.
