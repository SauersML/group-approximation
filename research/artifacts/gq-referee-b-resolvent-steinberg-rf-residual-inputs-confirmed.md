# Referee addendum (gq-referee-b, citation lens): the two K_2 inputs of the K_rf node, read at source

**Reviewed.** The source quotes in `resolvent-steinberg-rf-residual-is-infinitely-normally-generated`, which lane
gq-k2-q flipped at 69ed7e51a. My earlier report `gq-referee-b-resolvent-ring-corner-symbols-survive-in-k2.md`
(c73393b35) found steps 1–4 correct *given* (DS) and (vdK). At that time neither had been confirmed at source.

**PDFs read.** Both are in the session scratchpad at `gq/src/k2/`.
- `ds-survey.pdf`: Dennis–Stein, LNM 342. PDF page 1 is book page 241.
- `vdk.pdf`: van der Kallen, LNM 551. PDF page 1 is book page 77, and PDF page 2 is printed 78.

**Verdict: CONFIRMED.** Both quotes in the node match the printed pages verbatim, and both are applied inside their
hypotheses. The caveat in c73393b35 is discharged. The node is correct as flipped.

## (DS) Dennis–Stein, *The functor K_2: a survey of computations and problems*, LNM 342

- **The quote.** It spans the foot of book page 254 ("For example, if") and the head of page 255. The printed text
  reads: "W_m(F_q) denotes the ring of Witt vectors of length m over F_q, q = p^n, then (i) K_2(F_q[X]/(X^m)) = 1
  for all m ≥ 1 (ii) K_2(W_m(F_q)) = 1 if p is odd or if m = 1 (iii) K_2(W_m(F_q)) = Z/2Z if p = 2 and m ≥ 2."
  **Match.**
- **Section.** The passage belongs to §12, "K_2 for some local rings" (heading on p. 253). §13 begins on p. 255,
  after the quote. **Match.**
- **A second check from the same page.** Page 254 also prints the general formula: `K_2(A/P^m)` is cyclic of order
  `p^t`, where `t = [m/e − 1/(p−1)]_[0,r]` and `p^r` is the order of the `p`-primary roots of unity in the
  completion.
  - For `A = Z_(p)` we have `e = 1`. For odd `p`, `r = 0`, so `t = 0`. For `p = 2`, `r = 1`, so `t = 1` when `m ≥ 2`.
  - This agrees with (ii) and (iii) without passing through `W_m(F_p) = Z/p^m`.
  - `W_m(F_p) = Z/p^m` is standard but is not printed on these pages.
- **Independent stability at N ≥ 3.** Pages 253–254 state: "If A is a discrete valuation ring or a homomorphic
  image thereof, then K_2(A) and K_2(n,A) for n ≥ 3 are presented by the generators {u,v}, u,v ∈ A*, subject to the
  relations (S1) - (S7) [27, Theorems 2.3, 2.5]."
  - `Z/l^r` is a homomorphic image of the discrete valuation ring `Z_(l)`.
  - So the survey itself gives `K_2(N, Z/l^r) ≅ K_2(Z/l^r)` for `N ≥ 3`, the same range as (vdK).
- **Centrality.** Page 245, §1, reads: "In [69, §5] it is shown that K_2(R) is precisely the center of the Steinberg
  group St(R)." **Match** with the node's scope line.
  - The node's step 3 says "(Kervaire)". The survey attributes the result to [69, §5]. Either attribution is fine.

## (vdK) van der Kallen, *Injective stability for K_2*, LNM 551

- **Theorem 1, §1.1, p. 77.** The printed text reads: "Let R be a commutative ring with noetherian maximal spectrum of
  dimension d, d < ∞. Let n ≥ d + 2. Then the natural map K_2(n,R) → K_2(R) is surjective and the natural map
  K_2(n + 1,R) → K_2(R) is an isomorphism." **Match.**
- **The application is in range.**
  - `R = Z/l^r` is commutative, and its maximal spectrum is a single point, so `d = 0`.
  - Then `n ≥ 2`, so `K_2(N, Z/l^r) → K_2(Z/l^r)` is an isomorphism for every `N = n + 1 ≥ 3`.
  - The theorem is applied to no noncommutative ring. That matches the node's scope line.
