# Positive shift audit of the anchored-amplifier criterion

**Date:** 2026-09-11. Ordinary mathematics; no computation is used or needed.

## 0. Summary

One elementary instance transformation, replacing every term `h_a` by
`h'_a=(1-epsilon)h_a+epsilon I`, keeps locality, local dimension, term count
and polynomial descriptions, multiplies the promise gap by `1-epsilon`, and
makes every exact-satisfaction notion vacuous. Applied to the standard
inverse-polynomial QMA-complete reduction, it satisfies every construction
requirement that the anchored-amplifier region imposes on its amplifier,
except the YES margin (YES1). Conversely, shifting a reduction that witnesses
the quantum PCP conjecture satisfies the whole criterion for one reduction.

So the route `qpcp-from-anchored-amplifier` is equivalent to the root claim
through its YES-margin prerequisite, and nothing else in its prerequisite set
constrains an amplifier by itself. Exact combinatorial soundness carries
promise information only jointly with that margin, or on families whose YES
outputs are frustration-free, which the shift destroys. Robust combinatorial
soundness, with a positive satisfaction tolerance, is energy soundness up to
constants.

None of this refutes quantum PCP, and the syndrome technology of the region
keeps its intended use for an amplifier that also carries the margin.

## 1. Setting

As in `combinatorial-gap-and-rounder-give-energy-gap`: `H=(1/m) sum_a h_a` on
a nonzero finite-dimensional space, `0<=h_a<=I`, `m>=1`. `s*(H)` is the least
`|S|` such that some normalized `sigma` has `Tr(h_a sigma)=0` for every `a`
outside `S`. The least rounder constant is `0` if `lambda_min(H)=0` and
`s*/(m lambda_min(H))` otherwise (identity (CR4) of that claim).

## 2. The shift theorem

Fix a rational `epsilon` in `(0,1)` and put

```text
h'_a = (1-epsilon) h_a + epsilon I,   H' = (1-epsilon) H + epsilon I.   (PS0)
```

**(PS1)** `h'_a` acts on the support of `h_a`: identity on the remaining
tensor factors does not change locality. `0<=h'_a<=I`, `m` and the local
dimension are unchanged, and rational entries grow by `O(log(1/epsilon))`
bits.

**(PS2)** `h'_a>=epsilon I`, so `Tr(h'_a sigma)>=epsilon` for every normalized
`sigma`. No state satisfies any shifted term exactly. The only admissible
fault set is `S=[m]`, so `s*(H')=m` and `H'` has combinatorial gap one.

**(PS3)** `lambda_min(H')=(1-epsilon)lambda_min(H)+epsilon>=epsilon>0`. By
(CR4) with `s*=m`, the least rounder constant of `H'` is
`1/lambda_min(H')<=1/epsilon`.

**(PS4)** The map `x -> (1-epsilon)x+epsilon` is increasing and affine. YES
threshold `a` becomes `(1-epsilon)a+epsilon`, NO threshold `b` becomes
`(1-epsilon)b+epsilon`, and the promise gap becomes `(1-epsilon)(b-a)`.

**(PS5) Trivial syndrome data.** Put `H_syn=(C^2)^(tensor m)` and
`W psi = |1...1> tensor psi`, and let `B_a` be the projector onto flag `a`
reading `1`, with `N(a)={a}`, `C_0=1/epsilon`, `R=1`. Then:

- `W` is an isometry and the `B_a` commute, acting on distinct flag qubits;
- each port is a single flag qubit testable in its own region, and the data
  subsystem is untouched, so it lies in the commutant;
- `W^* B_a W = I <= (1/epsilon) h'_a`;
- the joint measurement returns `S=[m]` with probability one, so
  `E|S|=m<=(1/epsilon) sum_a Tr(h'_a rho)` for every `rho`;
- for every `S` other than `[m]`, the intersection of `ker h'_a` over `a`
  outside `S` is `{0}` and `W^* Pi_S W=0`, so every infeasible label has zero
  effect;
- the conditioned exactifier returns any normalized state, since condition
  (EX) quantifies over the empty set of terms outside `[m]`.

**(PS6) Robust soundness.** Say `H` has `(beta,eta)`-robust combinatorial gap
if every normalized `sigma` and every `S` with `Tr(h_a sigma)<=eta` for all `a`
outside `S` satisfy `|S|>=beta m`.

- If `H` has `(beta,eta)`-robust gap then `lambda_min(H)>=beta eta`. Given
  `sigma`, put `S_sigma={a : Tr(h_a sigma)>eta}`. Then `sigma` is
  `eta`-satisfying outside `S_sigma`, so `|S_sigma|>=beta m`, and
  `Tr(H sigma)>=(1/m) eta |S_sigma|>=beta eta`.
- If `lambda_min(H)>=b` and `0<eta<b`, then `H` has `(b-eta,eta)`-robust gap.
  If `sigma` is `eta`-satisfying outside `S`, then
  `b<=Tr(H sigma)<=(|S|+eta(m-|S|))/m<=|S|/m+eta`.

With `eta>0` fixed, robust combinatorial soundness is energy soundness up to
constants. Only the exact case `eta=0` is shift-vacuous.

## 3. The shifted standard reduction against each requirement

Let `R` be the reduction of `kitaev-local-hamiltonian-is-qma-complete` in
normalized form (Section 5), with thresholds `a<b` and `b-a>=1/p(n)`, and let
`R_epsilon` apply (PS0).

| requirement (node) | witness for `R_epsilon` |
| --- | --- |
| (LPC1), `locality-preserving-constant-combinatorial-gap` | constant locality, qubits, polynomial terms and bits; `beta=1` by (PS2) |
| cost clause (CR1), `amplified-hamiltonian-has-a-constant-cost-rounder` | `C=1/epsilon` by (PS3) or (PS5) |
| clauses 1-3, `amplifier-has-compatible-local-syndrome-effects` | data of (PS5) |
| (LSP1), `local-syndrome-port-domination-at-each-gadget` | `C_0=1/epsilon`, `R=1`, bounded horizon one flag |
| (EXA1), `syndrome-conditioned-exactifier-exists` | only `S=[m]` occurs; (EXA1) is vacuous |
| clauses 1-3, `amplifier-admits-a-uniform-local-kernel-resolution` | `T_[m]=I`, other `T_S=0`; `A_a=h'_a` is invertible, so `ran A_a` is the whole space; `delta=epsilon` |
| (ANC1), `bounded-horizon-syndrome-anchor-exists` | at every layer `t`, `b_t=N_t` (all flags read one) and `e_t>=epsilon N_t`, so `b_t<=(1/epsilon)e_t`; `r=1`, `A=1/epsilon` |
| (BSA1), `backward-syndrome-recursion-holds-for-the-amplifier` | `b_t<=(1/epsilon)e_t<=(1/epsilon)(e_t+b_(t+1))`; `L=1/epsilon` |
| (YES1), `amplifier-preserves-yes-energy-below-the-floor` | **fails**: YES outputs have `lambda_min=(1-epsilon)a+epsilon>=epsilon`, while the port-based floor is `beta/C=epsilon` and even the optimal floor `(1-epsilon)b+epsilon` exceeds the YES energy only by `(1-epsilon)(b-a)<=1/p(n)` |

In the anchor rows, `N_t` is the number of terms assigned to layer `t` in any
partition of the terms into layers. The inequalities hold term by term, so
the partition is irrelevant.

Every requirement except YES1 is met, and YES1 fails at a constant margin.
The region's port, exactifier, kernel-resolution, anchor and recursion
clauses therefore constrain an amplifier only in combination with the margin.

## 4. The converse

Let `R*` witness `quantum-pcp-constant-gap-local-hamiltonian`: thresholds
`a*<b*` with `b*-a*>=gamma>0`, constant locality and dimension. Then
`R*_epsilon` satisfies, for one reduction:

- (LPC1) with `beta=1`;
- the rounder criterion with the uniform constant
  `C=1/((1-epsilon)b*+epsilon)`, since every NO output has
  `lambda_min>=(1-epsilon)b*+epsilon` and (CR4) applies with `s*=m`;
- (YES1) with margin `beta/C-((1-epsilon)a*+epsilon)=(1-epsilon)(b*-a*)>=(1-epsilon)gamma`.

Together with the forward route, the conjunction of the anchored criterion
at a common reduction is equivalent to the root claim.

## 5. Normalization of the standard reduction

Kempe--Kitaev--Regev (arXiv:quant-ph/0406180v2, read 2026-09-11, Definitions
1-3 and Theorem 1) define `k`-local Hamiltonian as follows:
`H=sum_(j=1)^r H_j` on `n` qubits, `r=poly(n)`, `||H_j||<=poly(n)`, entries
with `poly(n)` bits, and thresholds `a<b` a constant apart. Theorem 1 proves
2-local Hamiltonian QMA-complete; the introduction credits the 5-local case to
Kitaev [KSV02] and 3-local to Kempe--Regev.

For (QPCP1), put `M=max_j ||H_j||` and `h_j=(H_j+M I)/(2M)`. Then
`0<=h_j<=I` and `(1/r) sum_j h_j = (H+rM I)/(2Mr)`, so the thresholds map to
`(a+rM)/(2Mr)` and `(b+rM)/(2Mr)`. The gap becomes `(b-a)/(2Mr)>=1/p(n)`,
with locality and qubit dimension unchanged.

## 6. Frustration-free outputs

The shift destroys frustration-freeness, so exact soundness keeps content on
families whose YES outputs are frustration-free. There the anchored template
naturally proves a statement with perfect completeness. A polynomial-time
reduction from a QMA-complete problem to Hamiltonians that are frustration-free
on YES instances and have `lambda_min>=1/poly` on NO instances places QMA
inside QMA_1. This needs the verifier's gate set to implement each output
term's measurement `{I-h_a,h_a}` exactly; the verifier measures a uniformly
random term on the witness. Aaronson, *On Perfect Completeness for QMA*
(arXiv:0806.0450, read 2026-09-11), gives a quantum oracle relative to which
`QMA` and `QMA_1` differ. A reduction of that kind would therefore not
quantumly relativize. That is a remark about proof technique: relativized
Hamiltonian reductions are not formalized here.

## 7. What is not claimed

- No refutation of quantum PCP, of the Bafna--Nguyen--Zhang amplifier, or of
  any syndrome construction for an amplifier that also carries a constant YES
  margin.
- No claim that the region's obstruction nodes are wrong. The qubit-pair,
  fixed-term-chain and joint-support results stand as proved.
- The shift is a vacuity witness for requirements stated without the margin.
  It is not a proposed amplifier.
