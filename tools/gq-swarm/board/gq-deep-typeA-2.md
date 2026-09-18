# gq-deep-typeA-2 board — DONE (09-18)
**Approach** (family: type (A) / oligomorphic permutation groups + Brin–Thompson registers).
Signature: "prime-shift permutation overgroup; register dilation locality".
**Established:**
- `gl-n-q-lies-in-prime-shift-permutation-group` (+ `-proof`), landed e53829d7e (lane proof, not reviewed):
  sigma = multiplicative automorphism of Q^x shifting Z-indexed primes (sigma(0)=0). GL_n(Q) <= K_n =
  <GL_n(Z), diag(2,1..1), sigma_n>, 2-transitive on P^(n-1)(Q); Aff(Q) <= A_1 = <x+1, 2x, -x, sigma>, 2-transitive
  on Q; <diag(2,..), sigma_n> = Z wr Z; K_n = image of the HNN of GL_n(Q) along the monomial group. Type (A) for
  these actions <=> finite presentation + one f.g. point stabilizer (both OPEN).
- artifact `gq-deep-typeA-2-register-dilations.md` (e53829d7e); root Attempt 18 (9b06d7d8c).
**Follow-up (09-18):** eb470001f `prime-shift-hnn-groups-are-not-finitely-presented` (Pi_n not fp; A_1/K_n fp only via
  hidden relation m_r in <<unipotents>>; Pi_1 -> A_1 injective => no finitary perms, ab = Z/2 x Z^2) and
  `prime-shift-dilation-normalizers-are-nowhere-continuous` (any prime-shift normalizer of the dilations is c*sigma,
  nowhere continuous); root Attempt 18 follow-up e7fa741a6.
**Needs:** decide injectivity of Pi_1 -> A_1 (the single open question for this route).
**Dead:** gq-bt-kojima Spark 3 (register with bounded x p), three forms: slot/placeholder formats (+1/p loses
  uniform depth, undefined on orbit closure); shifted formats (radix sets eventually nonincreasing => finitely many
  primes); per-prime registers with shared overflow (actor must contain Aff^+(Q)). Radix-swap and placeholder
  dilation (§3.3–3.4) are bounded rewrites and reusable.
**Sparks:** decide finite presentation of A_1 (smallest case). Natural-action obstructions do not apply (sigma is
  continuous for no real or p-adic topology).
