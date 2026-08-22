---
rg: 2
id: hadamard-pcpp-affine-unsafety-proof
kind: route
title: Xor perfect PCPP proofs and invoke proximity soundness on the rejected encoded answer
target: hadamard-pcpp-reflects-affine-unsafety
requires:
  - dfnqxy-answer-reduction-does-not-preserve-affine-safe-support
---

Definition 6.7 identifies the PCPP language with pairs of Hadamard encodings
of accepted answer pairs.  Two distinct Hadamard words have relative
distance `1/2`.  Hence an encoding of a rejected pair is at distance at
least `1/4` from the two-block accepted language, which meets the stipulated
PCPP threshold `gamma<=1/4`.

Choose arbitrary perfect proofs for the finitely many positive outcomes in
an odd-xor witness.  Their bitwise xor is a legitimate (not necessarily
honest) candidate proof.  PCPP soundness supplies a random string on which
the rejected encoded pair together with that xor proof is rejected.
Perfect completeness accepts every honest pair/proof on the same random
string.  The completeness construction in Theorem 6.9 computes the answer,
its Hadamard word, and its proof, so restriction to the sampled coordinates
is a deterministic refinement of the original source PVM.  Positivity of
the source atom therefore implies positivity of the corresponding restricted
answer atom.  Finally, both Hadamard encoding and coordinate restriction are
linear, so the rejected response is the odd xor of those positive accepted
responses.  This proves affine unsafety of that one `Verify` context.

