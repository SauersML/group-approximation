# gq-steinberg-q board
**Approach** (family: linear characteristic / K-theory). Signature: "Leavitt doubling swindle kills unstable Tate symbols".
**Established** (refereed): `leavitt-pairs-embed-sl-n-q-in-steinberg-groups` (6431e0989; PASS a/b/c): SL_N(Q) <= St_(6N+1)(S)
  for any S ⊇ Q with a Leavitt pair. Route `gl-n-q-explicit-via-steinberg-group-of-resolvent-ring`: St_(6n+7)(R_L) fp (T) ⊇ GL_n(Q)
  -> all requires established -> Problem 2.7 root reached.
**Established** (lane proofs, elementary): `leavitt-resolvent-ring-is-fp-and-contains-q` (R_L part 1, checked by referee-b);
  `st-n-of-ring-quotient-adds-one-relator-per-ideal-generator` (St_n(F/I) = St_n(F)/<<x_12(ρ_t)>>, n>=4; nine R_L words in route);
  `leavitt-centralizer-units-are-elementary-in-rank-three` (3215a81d2): Q^x scalars central in E_m(S), m>=3.
**Established** (refereed a,b; 8a94c3a06): `leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1`: W factors in E_3N (no Whitehead),
  coefficients in any subring centralizing the pair; => every GL_n(Q) in ONE group St_10(R_L)
  (route `gl-n-q-all-n-in-st-10-of-resolvent-ring`).
**Source record**: artifacts/gq-steinberg-q-krstic-mccool-source.md (KrM Thm 3, n>=4 sharp; primary paywalled).
**E_m(R_L) fp?** undecided — artifacts/gq-steinberg-q-e-n-of-resolvent-ring-status.md (not both E_m and E_m/Q^x fp;
  conditional non-fp if {N+1, Q^x} ⊆ K_2(R_L) not f.g.; heuristic PV: K_2(R_L) ≅ Q^x, K_1(R_L) ≅ Z).
**Needs**: primary text of Krstić–McCool (MSI proxy) to write St_10(F_6)'s presentation; a PV sequence for O_ψ rings.
**Dead**: HNN/Higman encodings of the prime chain (not natural).
**Round 3 (09-18, coordinator: is R_T f.p.?)** — landed 1111ca113, under review (referee-a, referee-b):
- `bounded-harmonic-rings-are-not-finitely-presented`: harmonic crossed products (u_s, finite-range h_i, f = 1/(1+ℓ∘π))
  are NOT f.p.; no f.p. ring mapping to them contains Q; E_N (N>=3) never f.p. Truncation f -> f_k keeps finitely
  many identities, kills large primes. Refutes `sl3-toeplitz-harmonic-elementary-groups-are-fp` (R_T dead as G host).
- `leavitt-tuples-make-rational-scalar-powers-elementary`: Leavitt (1,d)-tuple ⇒ (Q^x)^(d-1) I ⊆ E_m ⇒ scalar budget fails.
- Squeeze + open design question: artifacts/gq-steinberg-q-harmonic-truncation.md.
