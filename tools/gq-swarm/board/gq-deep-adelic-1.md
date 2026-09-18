# gq-deep-adelic-1 board
**Approach** (family: operator algebras / K-theory, adelic valuations vs tame symbols; sig "tracial harmonic ring K-budget").
The ring route needs a f.g. simple R ⊇ Q with rational scalars non-elementary (gq-en-ring Need). Every ring host on
main is purely infinite ([1] = 2[1] kills scalars in K_1). First falsifiable step: a TRACIAL f.g. simple ring ⊇ Q
(harmonic function inside C(X) ⋊_σ Z, X a minimal subshift) with Fuglede–Kadison keeping Λ_N(R) ⊆ {±1}; then test
K_2 via the ABC twisted-Laurent fibration.
**Established** (lane proofs, not refereed; landed 1b6190e97, 83261b5be; review requested from gq-referee-b):
- tracial-harmonic-ring-keeps-rational-scalars: R_h = Z<u^±1, letter cylinders, f> ⊂ C(X) ⋊ Z is f.g., simple,
  centre Q, contains Q, Λ_N(R_h) ⊆ {±1}; GL_n(Q) ≤ PE_N(R_h) = E_N(R_h)/{±I}.
- laurent-rational-symbols-block-fp-elementary-groups (OBSTRUCTION): B ⊇ Q unital, σ fixes Q, Q^x → K_1(B) with
  infinitely generated image (e.g. B commutative) ⇒ λ ↦ {λ,u} embeds that image in K_2(B[u^±1;σ]) ⇒ no E_N, N ≥ 3,
  is finitely presented. Kills R_h and every Z-crossed product over a commutative Q-algebra.
- infinitely-generated-symbols-block-fp-elementary-groups: E_N(R) f.p. (N >= 3) ⇒ the image of K_2(N,R) in stable K_2(R)
  is f.g. and contains every Steinberg symbol (Neumann + Kervaire; no rank-N centrality). Attempt 5 added to
  q-algebra-with-fp-simple-projective-elementary-group.
**Round 2** (coordinator target: UHF-type host from odometer models; split with gq-en-ring: I take groupoid
readings + non-cyclic crossed products; landed a922d082a, unrefereed): fg-q-rings-have-no-matrix-representations;
af-groupoid-rings-have-no-fg-subring-containing-q (AF/UHF tail groupoids: no f.g. ring ⊇ Q, any coefficients);
matrix-corner-laurent-rings-block-fp-elementary-groups (R ≅ M_k(graded S with degree-one unit, tracial S_0) ⇒ no f.p.
E_N; kills crossed products whenever the odometer chain has an indicable finite-index subgroup, perfect Γ included).
Verdict artifact gq-deep-adelic-1-uhf-class-verdict.md. REMNANT: FAb-along-chain Γ (SL_3(Z)); risks R1 cylinder
corners, R2 torsion index units (Q^x ⊗ Z/d symbols).
**Round 3** (SL_3(Z) remnant; landed f9dbfcd34, unrefereed): harmonic-elimination-puts-q-in-odometer-crossed-products
(Q in ⟨u_s, one harmonic f⟩ over ANY odometer factor); sl3-congruence-transfer-kills-abelianization (transfer
Γ(d)^ab → Γ(d^2)^ab = 0, n>=3); sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational (FIRST CANDIDATE R_T: f.g. simple,
centre Q, Λ_N ⊆ ±1, K_2(Q) dies, block/group units have trivial rational symbols). OPEN:
sl3-toeplitz-harmonic-ring-meets-the-uhf-k-budget (letter-cylinder corners R1, general units R2). Artifact
gq-deep-adelic-1-sl3-remnant.md. Pure odometer ring R_K: Q ✓, tracial ✓, simplicity open (idempotent-poor).
**Needs** (open, anyone): a f.g. simple ring R ⊇ Q with the "UHF K-budget": ker(Q^x → K_1(R)) f.g. AND the symbols
{λ, x} (λ ∈ Q^x, x ∈ R^x) generating a f.g. subgroup of K_2(R). U_Q = colim M_(n!)(Q) has it but is not f.g.
**Dead**: Z-crossed products over commutative Q-algebras (above); standard adelic models (A_f^n ∪ ∞, solenoid,
∏_p P^(m-1)(Q_p), RCWA(Z^n)) for the standard copy — already covered by germ-extensions-omit-standard-gl-n-q (c).
**Sparks**: crossed products by a PERFECT acyclic f.g. group acting minimally, measure-preservingly, with divisible
coinvariants C(X,Z)_Γ (then {λ, u_γ} = 1 and K_2(Q) ⊗ coinvariants = 0); Toeplitz subshifts over the universal
odometer Ẑ (adelic: [1] divisible by every integer). The ring must avoid units of nonzero "index" class.
