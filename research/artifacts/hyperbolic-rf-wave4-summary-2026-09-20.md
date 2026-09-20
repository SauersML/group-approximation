# Problem 141: fourth parallel campaign

20 September 2026. **The full problem is not solved.** No nonidentity
element in a word-hyperbolic group has been proved invisible in all
finite quotients in this campaign.

The preceding campaign excluded several particular constructions. This
one controls entire refinement families and determines the canonical
central mark in an explicit presentation.

**The decisive new result is an actual finite detector:** a certified
class-five group of order7^28 preserves the canonical centre with order7.
Therefore c0 mod7 virtually splits on a normal cover of index7^27. The
selected mod-seven central mark cannot supply the proposed invisible
element. This neither proves residual finiteness of the base K7 nor
settles central orders at other primes.

## Verified progress

| Result | Scope and remaining gap |
|---|---|
| The kernel N of H31 -> PSL2(31) x C5 is perfect. | Excludes every solvable-kernel refinement of this specified quotient. A different quotient can still induce a nonsolvable image of N. |
| H1(M;F5)=0 for the entire kernel M of the specified PSL2(19)^2 quotient. | Excludes all five-group refinements, also for the nonzero central five-twists. Mixed-prime solvable and nonsolvable refinements remain. |
| The full dual-number image Sp4(F7[t]/t^2) is perfect with trivial Schur multiplier. | Excludes all central detectors whose indicated quotient base is this actual image, not only Steinberg pushouts. Other finite bases remain. |
| The canonical cover has a marked six-face presentation, K7_ab=C7^4, and z lies in gamma5(B_c0). | Every quotient of nilpotency class at most four kills the mark; this does not control all nilpotent or finite quotients. |
| A finite class-five group of order7^28 detects z. | The preceding nilpotency bound is sharp. The mod-seven extension virtually splits; unbounded central orders and other primes remain unresolved. |

Proofs and exact certificates:

- `hyperbolic-rf-wave4-h31-perfect-kernel-2026-09-20.md`
- `hyperbolic-rf-wave4-detectors-2026-09-20.md`
- `hyperbolic-rf-wave4-visibility-2026-09-20.md`
- `hyperbolic-rf-wave4-class-two-2026-09-20.md`
- `hyperbolic-rf-wave4-nilpotent-mark-2026-09-20.md`
- `hyperbolic-rf-wave4-class-five-detector-2026-09-20.md`

The H31 computation uses two independent exact rank algorithms. The
PSL2(19) proof checks a projective-generator certificate and all 64 tensor
summands, so its conclusion concerns the full kernel, not just a selected
invariant sector. The matrix-image proof uses exact adjoint and exterior
square calculations. The class-four conclusion uses the exact marked
Lie ideal; a rank389 ideal in the free dimension406 algebra contains z.
Each main result received a separate mathematical review and replay.
The finite detector also has a standalone JSON-only verifier: it checks
the Lie axioms, exact class, generation and all six marked face relations
without trusting either quotient-construction algorithm.

The broader obstruction is unchanged: these statements must not be
combined into a claim that the covered families exhaust all finite
quotients. A solution still needs a universal invisibility/persistence
argument, an actual different counterexample, or a proof of residual
finiteness for all hyperbolic groups. The root remains OPEN.

Graph loading and dependency verification are recorded separately in
`hyperbolic-rf-wave4-validation-2026-09-20.json`. Concurrent unrelated
changes may produce global findings; graph state is not mathematical
certification or proof-assistant verification.
