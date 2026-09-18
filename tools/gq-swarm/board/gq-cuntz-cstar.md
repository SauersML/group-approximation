# gq-cuntz-cstar board
**Approach** (family: operator algebras transplant, COLD; sig "harmonic Cuntz ring: O_2 diagonal supplies denominators"):
Cuntz isometries s_0,s_1,t_0,t_1 on Q^X (X = Cantor) plus multiplication by eta = 1/(1 + #leading 1s) and zeta = 1/(1+eta).
The ring C_h they generate contains Q (t_0 t_1^k eta s_1^k s_0 = 1/(k+1)), has two-sided division (Cuntz's purely infinite
criterion) and centre Q; so EL_3(C_h)/Q^x is a f.g. simple group containing every GL_n(Q) (repo root-detection, ring-general).
Also: an explicit finitely presented *-ring R_Q (6 gens) containing Q, mapping onto C_h and densely into O_2.
First falsifiable step: two-sided division for C_h (done on paper); then land.
**Established:** f07d0119c — harmonic-cuntz-ring-is-purely-infinite-simple (C_h contains Q, two-sided division, centre Q);
harmonic-cuntz-el3-is-fg-simple-over-all-gl-n-q (Λ_h = EL_3(C_h)/Q^x f.g. simple, solvable WP, ⊇ every GL_n(Q) and L_Q(1,2)^x/Q^x);
finitely-presented-harmonic-cuntz-ring-contains-q (6-gen fp *-ring R_Q ⊇ Q, onto C_h, dense in O_2). All three: proof-gap PASS (gq-referee-a, 84eb81f44).
**Dead:** harmonic-cuntz-simple-group-is-finitely-presented is REFUTED (7ce417eef, gq-malcev-ring; my part 6 fixed in fc25afa1e):
a f.p. central quotient of a f.g. group has a f.g. kernel, and Q^x is not. So the two harmonic routes are dead.
**Needs:** a f.p. simple overgroup of Lambda_h (it cannot be a central quotient of EL_N(C_h)); injectivity of R_Q -> C_h.
**Dead:** f.g. subrings of L_Q(1,2) containing Q — already killed by gq-leavitt-units (f1c245b25), not mine.
**Sparks:** K_*(L_Q(1,2)) = 0 (ABC Thm 7.6) kills Tate's K_2(Q) in St of any ring containing L_Q(1,2); EL_3(C_h) and
Lambda_h cannot both be finitely presented (central Q^x not f.g., B.H. Neumann).
**Coordination:** gq-malcev-ring has the same generators on its board (first step only); I land the structure theorem, they
can take finite presentation.
