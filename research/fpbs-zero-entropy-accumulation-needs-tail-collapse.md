---
rg: 2
id: fpbs-zero-entropy-accumulation-needs-tail-collapse
kind: claim
title: For a zero-entropy quasi-geodesic ray code with a finite invariant measure on a hyperbolic group, forward S-words that are tail-equivalent (equal after shifts) and share an endpoint have at most |Stab| distinct past endpoints, so asymptotic pairs of the symbolic system (one right ray, many left extensions) are invisible to the current, and essential accumulation needs infinitely many tail-inequivalent typical futures with a common endpoint; codes with finitely many tail classes per endpoint die
distinct_from:
  fpbs-ray-code-deaths-depend-only-on-the-current: that shows the current decides and that at zero entropy the past is a function Psi of the forward S-word, and it proposed right-asymptotic pairs of a Toeplitz system as the source of accumulation. This node proves that proposal cannot work (Theorem 2) and replaces "infinite family of forward words" by the strictly smaller count of tail classes (Theorem 1), which is what a survivor must make infinite.
  fpbs-finite-to-one-quasigeodesic-ray-codes-die: that kills finite fibres of positions (FT) at any entropy. At zero entropy this kills infinite fibres too, as long as they fall into finitely many tail classes; a fibre may be uncountable and still die here.
---

**ESTABLISHED (written proof: `research/fpbs-zero-entropy-accumulation-needs-tail-collapse-proof.md`).** The proof
uses Proposition 4 and Theorem 1 of `fpbs-ray-code-deaths-depend-only-on-the-current`, the Morse lemma, and
finiteness of stabilizers of non-loxodromic boundary points.

**Why this matters for the flagship.** For a cocompact `Sp(n,1)` lattice (property (T), fixed price open), the
Bevilacqua--Bowen (BB) ray-code route was left with one open statement: an essentially accumulating current over a
Dini-singular class. The zero-entropy branch is forced to be Dini-singular (dimension zero), so it is the natural place
to look. The proposed first test was a Toeplitz code with **right-asymptotic pairs**: one right ray with infinitely
many left extensions whose group paths diverge in the past. This node shows that test is dead at its first step, for
every zero-entropy system, and names the only mechanism left.

## Setting

As in `fpbs-ray-code-deaths-depend-only-on-the-current`. `Gamma` is hyperbolic with finite generating set `S`. Refined
positions `p ∈ X^#` carry the `S`-letter process `a_j(p) ∈ S`, refined paths `P_p` with `P_p(0) = 1`, (UQ) with
constants `(lambda, c)`, endpoints `zeta^{-#}(p)`, `zeta^#(p)`. `rho^#` is a finite `T^#`-invariant measure of
**entropy zero**. `nu` is the forward class and `nu^-` the backward class, both assumed nonatomic. `mu_R` is the
current and `mu^eta` its conditionals.

**Forward words and tails.** `w(p) = (a_0(p), a_1(p), ...) ∈ S^N` is the forward `S`-word. Two words are
**tail-equivalent**, `w ~ w'`, if `sigma^m w = sigma^{m'} w'` for some `m, m' >= 0` (`sigma` the shift).

By Proposition 4 of the parent node there is a conull `T^#`-invariant Borel set `X_1` and a Borel `Psi` with
`zeta^{-#}(p) = Psi(w(p))` for `p ∈ X_1`.

**Tail multiplicity.** For `eta ∈ dGamma` and `r >= 0`, let `W_r(eta)` be the set of pairs `(h, w(q))` with
`h ∈ B(1, r)`, `q ∈ X_1` and `h zeta^#(q) = eta`. The **tail multiplicity** `tau_r(eta)` is the number of
tail classes met by the words in `W_r(eta)`.
- **(FTM)** For `nu`-a.e. `eta` and every `r`, `tau_r(eta) < infinity`.

## Results

**Theorem 1 (tail-equivalent futures carry finitely many pasts).** Let `eta` have finite stabilizer (true off a
countable, hence `nu`-null, set). All pairs `(h, w) ∈ W_r(eta)` whose words lie in one tail class give lines with at
most `|Stab(eta)|` distinct backward endpoints `h Psi(w)`.

**Corollary 1' (finite tail multiplicity kills).** (FTM) implies (LF_mu). Hence, by Theorem 1 of
`fpbs-ray-code-deaths-depend-only-on-the-current`, every imp action with a boundary map into `nu` has totally
dissipative diagonal, and no ergodic such action is PDR. Each tail class is countable. But the position fibres over
`eta` may be infinite, and even uncountable, since positions can carry more than their `S`-word. So this strictly
extends the zero-entropy case of `fpbs-finite-to-one-quasigeodesic-ray-codes-die`.

**Theorem 2 (asymptotic pairs are invisible to the current).** Let `(Y, sigma)` be any zero-entropy subshift (for
example a Toeplitz system) spelled into `Gamma` by a (UQ) code. Right-asymptotic pairs and, more generally, all left
extensions of one right ray lie in a single tail class, so by Theorem 1 they contribute at most `|Stab(eta)|` atoms to
`mu^eta`. Only one of those left extensions lies in `X_1`, and the others form a `rho^#`-null set. The Toeplitz
asymptotic-pair test of the parent node can never produce essential accumulation.

**Theorem 3 (what essential accumulation needs: tail collapse).** Essential accumulation at zero entropy holds
exactly when (LF_mu) fails. By Corollary 1' it forces **tail collapse**: for `nu`-positively many `eta` there are
infinitely many pairwise tail-inequivalent typical futures `(h_k, w_k) ∈ W_r(eta)` with pasts `h_k Psi(w_k)` taking
infinitely many values in some `K_r(eta)`. By the Morse lemma their group paths are eventually within
`D = D(lambda, c, delta, r)` of each other. So the code must have infinitely many distinct typical futures whose
paths fellow-travel at bounded offset without ever agreeing as words.

## Calibration

- **Toeplitz, odometer and Sturmian codes with a fixed spelling per letter** on the lattice codes of
  `fpbs-quasiconvex-null-lattice-odometer-class-dies`: finitely many tail classes per endpoint off a null set. (FTM)
  holds, and they die.
- **Toeplitz respellings** (Theorem 3 of `fpbs-backward-locally-finite-ray-codes-die`): the digit-driven choice
  between `s` and `s_1 s_2` makes continuum many tail classes, so (FTM) fails. But the pasts do not separate (the
  relation `R` is unchanged), so (LF_mu) still holds. Tail collapse is necessary but not sufficient, and Theorem 3
  asks for both conditions.
- **Free group with free basis and geodesic refined paths.** Geodesic rays with a common endpoint agree after a shift,
  so `tau_r = 1`. Tail collapse needs relations in `Gamma`, for example independent flips across the two sides of
  relator cells.
- **Geodesic-flow Markov code (positive entropy).** Theorem 1 does not apply, because `Psi` does not exist. Its
  accumulation comes from positive entropy, which is consistent with the parent's Theorem 3.

## What this leaves (named open statement)

**Tail-collapsing zero-entropy codes.** On a cocompact `Sp(n,1)` lattice, is there a zero-entropy (UQ) ray code with
a finite invariant measure, a quasiconvex-null class, and tail collapse whose pasts separate, such that some imp
action over its class has a conservative diagonal? A candidate must couple infinitely many tail-inequivalent typical
futures at bounded offset, for example cell flips driven by an odometer, and must make the past depend on the flip
pattern. Remark 4 of the proof explains why respelling fails: it collapses tails but leaves the coarse letter path,
and so the past, unchanged. The separation of pasts has to come from coarse futures that are tail-inequivalent and
still fellow-travel, which needs relations of `Gamma`.
