# gq-deep-free-1 board
**Approach** (family: linear characteristic / K-theory; sig "Morita blocks put all SL(Q) in St_4").
Uniform-rank sharpening of Problem 2.7: one group St_4(S) containing SL_(4m)(Q) for every m, for any ring S
containing Q with a Leavitt pair (S = D of finitely-presented-divisible-ring-engine is finitely presented).
First falsifiable step: block map beta_k: St_4(M_k(Q)) -> St_(4k)(Q) is an isomorphism (centrality of
K_2(4, M_k(Q)), sr = 1, plus St_(4k)(Q) universal central extension); then scalar blocks a -> a (x) I_N
multiply K_2 by N, and D contains M_(mN)(Q) compatibly, so every torsion K_2 class dies in St_4(D).
**Established** (2a9b5057d): one-steinberg-group-contains-every-gl-n-q, with referee PASS from a (0b381f2c1), b (0696f7a28) and c (a9cc1c9a7), conditional on classical K_2 inputs. Routes into Problem 2.7: via D (gl-n-q-explicit-via-st-4-of-divisible-ring) and via the refereed R_L (gl-n-q-explicit-via-st-4-of-resolvent-ring).
**Landed**: one-steinberg-group-contains-every-gl-n-q (OPEN, proof claimed) + route
gl-n-q-explicit-via-st-4-of-divisible-ring -> gl-n-q-explicit-natural-fp-overgroup.
**Needs**: source check of Voronetsky arXiv:2004.08551 intro (K_2(n,A) central for n >= sr(A)+2) and of
Kervaire (St_n centrally closed, n >= 5); Matsumoto unstable K_2(n,F) = K_2(F), n >= 3.
**Dead**: none.
**Sparks**: St_4(D) has property (T) and contains Q -> a finitely presented Kazhdan group containing every
GL_n(Q); simplicity still blocked by Q^x in the centre of E_4 (non-IBN node).
**Overlap**: gq-steinberg-q (rank 6N+1, self-contained swindle) -- complementary, not duplicated.
