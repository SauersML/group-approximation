# bh-free-39 (free lane; seed: stabilization kernel U_3(R_L))
**Direction (09-18):** attack U_3(R_L) = ker(K_2(3,R_L) -> K_2(R_L)) directly: exhibit an element or prove U_3 = 0.
**Own attempts (not landed, now subsumed):** U_N = ker Σ^g for every Leavitt half g (so U_N avoids every proper
cylinder corner, which bh-free-04's 3b2db8113 already covers); natural candidates all vanish (central symbols {λ,v}_N on
commutator units, orthogonal Dennis–Stein commutators [X_ij(eae*), X_ji(fbf*)], the doubling θ_* kills U_N). No
nontrivial element found; every direct proof reduction was circular with surjective stability.
**Resolved by peers:** gq-infinite-primes eecdc0a2f `leavitt-resolvent-k2-stability-holds` proves U_N = 1 for all N >= 3
(relative Khanh comparison mod C = j(K_2(n-1)), n >= 5). I checked it independently (Khanh raw-criterion l.430–495,
frame cone, sign lift ω_12 = w_12(1) d_1 with [ee*-ff*, ef*+fe*] = -1, K_1 one-step item 3): agree. Only gap I found
(M_j > D in the separated-tag multiplier) was already fixed by gq-referee-a N4 (f65202ed8). Referees a, b: PASS.
**Landed c9078cd61:** `steinberg-groups-of-r-l-are-quasisimple` (+ -proof). With U_N = 1:
- every proper normal subgroup of St_N(R_L) is central; Z(St_N) = φ^-1(Z(E_N)); St_N/Z ≅ PE_N(R_L) is the ONLY simple
  quotient (Steinberg-quotient host route through R_L closed: U_N = 1 removes bh-free-04's "quotient of U_N" case);
- H_2(St_N(R_L)) = 0 (vdK LNM 551 §8.1, read at source; N = 3,4 via refinement), so St_N is the universal central
  extension of E_N and PE_N: H_2(E_N(R_L)) ≅ Q^x, H_2(PE_N(R_L)) ≅ Z(St_N) (not f.g.) — second proof PE_N not f.p.;
- every GL_n(Q) embeds in St_10(R_L) meeting its centre trivially ⇒ GL_n(Q) ↪ PE_10(R_L) (one f.g. simple group, solvable WP).
  So St_10(R_L) is an f.p. Kazhdan quasisimple group containing every GL_n(Q) off the centre; the BH gap there is
  exactly the non-f.g. centre.
**Status:** finished (one-shot fork).
