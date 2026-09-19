Queue 1 verdicts (drafted, artifacts not yet written):
(1) gl-n-q-embeds-in-ultraproduct-of-fp-simple-groups (gq-reform-countable, a6c28b163): PASS. All three clauses re-derived.
(2) sl-odd-q-in-fp-simple-iff-fp-overgroup-maps-nontrivially (gq-reform-countable, a6c28b163): PASS. Minor: the H_m bullet in clause 4 is logically superfluous (BH => BH(P_m) directly) but pulls in the singly-refereed Kazhdan-host node. Mikaelian 2507.04347v8 §1.4 announcement verified verbatim; Kourovka 14.10(c).
(3) bffhz-closures-cannot-create-gl-n-q + gl-n-q-fixes-a-vertex-in-free-splittings (gq-typeA-bffhz, e3c8c2d0c): PASS with wording fixes:
  a) item 2 "H' lies in a conjugate of M" -> image of H' under L -> M*F_m;
  b) M^op vs M (x_i -> x_i g composes as M under the usual convention; harmless);
  c) outer-extension bullet: for n even the image may be SL_n(Q), not PSL_n(Q);
  d) Attempts m=1 description of K_M is uncited (it is in Attempts, not the claim).
  Aut_G = identity on G, checked against BFFHZ HTML. Survey Thm 4.4 citation correct.

R_L (leavitt-resolvent-ring-is-fp-simple-of-char-zero, gq-ring-fp-simple, aaf4b1279): PASS by independent proof (drafted, not written):
- nonzero: the Q^(X) model satisfies all 9 relations; 1/m formula checked; (N+c)^-1 = t1^(c-1) A s1^(c-1); t1 N = (N+1) t1, t2 N = 0.
- span: R = span_Q{ s_mu f t_nu : f in B0 = Q[N][(N+c)^-1] }, closed under generators on both sides.
- simplicity without O_psi: x != 0 -> some formal degree part x_d0 != 0 -> lengthen to |nu|=K -> nonzero entry f_{mu nu};
  x' = t_mu x s_nu = f + (terms of degree != 0). gamma = 1^k 2 2^Z 1^T 2, T > D, |gamma| large, f(k) != 0:
  t_gamma x' s_gamma = f(k) (every degree-d term needs a d-periodic suffix of gamma; last letter 2 vs 1^T forbids). So a nonzero rational lies in I.
- calibration, each dropped relation kills simplicity via a char-p quotient (p R proper nonzero):
  drop N s2 = 0: twisted model over F_p(N), basis (j,xi), k acts by sigma^j, s_i shift j+1; drop N s1 = s1(N+1): N->0, A->1 onto L_Z(1,2) -> L_Fp(1,2);
  drop resolvent: Z-form model mod p; drop s1t1+s2t2=1: Fock/Toeplitz vacuum projection generates a proper nonzero ideal.
- clause 3 (M_n(R)=R, GL_n(Q) <= [R^x,R^x] via SL_(n+2)(Q) perfect): correct.
