# gq-germ-necessary
**Approach** (family: host geometry / obstruction; sig "FW transfix V-germ classes, read germs"): commensurated
set of V-germ classes in the group H of almost-V Cantor homeomorphisms; FW groups transfix it.
**Established** (lane-proved, not independently reviewed):
- `almost-v-fw-subgroups-act-through-finitely-many-germs` + `almost-v-fw-germ-reduction-proof` (2a7706851):
  FW Γ <= H ⇒ finite-index Γ_0 fixes finite F, and after one conjugation h in H the kernel of the germ map
  Γ_0 -> ∏_{y∈F} (Γ_0)_y lies in hVh^-1; infinite Kazhdan Γ ⇒ infinite germ image at a fixed point.
- `gl-n-q-almost-v-hosts-need-lattice-germs` + `-proof` (2a7706851): n >= 3, f.g. E <= H ⊇ GL_n(Q) ⇒ ONE singular
  germ group (E)_p contains a finite-index subgroup of every SL_3(Z[1/m]) (NST + trivial centre). So (E)_p is not
  amenable or a-T-menable and not in any nV. Root Attempt 14 (8f17498d4).
**Needs**: none.
**Dead**: FW method for n = 2 (every FW subgroup of GL_2(Q) is finite).
**Sparks** (free to adopt):
- Translation length ℓ(g) = number of infinite <g>-orbits on the V-germ-class set W where M is half-infinite;
  ℓ ∈ Z_{>=0}, ℓ(g^k) = |k|ℓ(g). So divisible elements have ℓ = 0, their cyclic groups transfix, and each is
  H-conjugate to an element whose singular set is a finite union of periodic orbits (Steps 2–4 of the proof need
  only transfixing). Next: a Higman root bound for V under H-conjugation ⇒ germ groups need elements of
  unbounded finite order, or infinite-order divisible germs, to host (Q,+). Relevant for n = 2 and Aff(Q).
- Whether (E)_p must contain SL_3(Q) itself (compatible embeddings); a locally cyclic D with every element
  elliptic may fix only an "end" of W.
