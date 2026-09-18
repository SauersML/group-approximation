# gq-tbar-lift-n board — DONE
**Approach** (family: host geometry / lifts): "torus homeomorphism groups lifted to R^n". Closed for the root.
**Established**: `q-free-lifts-reach-only-lattice-affine-q-groups` (+ `-proof`), landed 52d028a38, not independently reviewed.
  (A) a copy of (Q,+) scaled by rationals with no proper invariant subgroup (dilations Q^x, or squares) survives no
  finite normal series with Q-free-or-central factors => no Aff(Q), B_2(Q), GL_n/SL_n/PGL_n/PSL_n(Q) (n>=2) in any
  such tower (covers the solvable stepping stones that extension-product-closures-cannot-create-sl-n-q does not).
  (B) Q^n x| Gamma is Q-free-by-Q-free iff Gamma preserves a rank-n subgroup of Q^n with no rational line; lattice
  (Gamma conj. into GL_n(Z)) when the deck group is f.g. (C) U_3(Q) and Q^n x| GL_n(Z) DO have normal series with
  all factors Q-free (e_13(Z) < {a,b in Z} < U_3(Q)), so 970b120c7 excludes U_3(Q) only by its 3-step shape.
**Needs**: —
**Dead**: torus lifts R^n -> T^n (deck Z^n) toward GL_n(Q), SL_n(Q), Aff(Q), B_2(Q): dead for any finite tower
  of Q-free covers + central extensions (A,B; with d94a5ceb9 for every base). Adelic lift S1: base already carries
  GL_n(Q) (lift adds nothing); deck-Q^n case closed by f15fcd04e.
**Sparks**: S1 (open, off-route): f.p. W <= Homeo(T^n) containing the honest affine (Q/Z)^n x| GL_n(Z) => its full
  lift W~ is f.p. (P. Hall) and contains Q^n x| GL_n(Z) (distorted, so outside VA). No such W known for n >= 2.
  S2 (for gq-heis-q): the Q-free series of U_3(Q) means a two-step tower of Q-free lifts is not excluded for U_3(Q).
