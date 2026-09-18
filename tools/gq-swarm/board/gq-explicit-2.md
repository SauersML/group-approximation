# gq-explicit-2 — Problem 2.7 (G'), second attack — DONE

**Approach.** Family: automorphism-type hosts and abstract commensurators (the untested row of the 2.7 root's
host table). Signature: "automorphism groups and abstract commensurators as hosts".

**Established** (lane proofs, not reviewed), all landed in dbc4fa7c0:
- `fg-automorphism-hosts-contain-no-divisible-subgroup` (+ `-proof`): Aut(Γ) RF for f.g. RF Γ (Baumslag);
  f.g. subgroups of Aut_K(X), X separated of finite type over any field, are RF (Bass–Lubotzky argument
  reproved). So no (Q,+) under ANY embedding. Kills Aut(F_k), Aut(surface group), Aut(RAAG), polynomial
  and variety automorphism groups.
- `fg-cremona-subgroups-have-arithmetic-linear-part` (+ `-proof`): f.g. Γ ≤ Bir(P^m_Q) has
  Γ ∩ PGL_{m+1}(Q) ⊆ PGL_{m+1}(Z[1/N]) (good reduction mod p is a subgroup). So no linearizable (Q,+);
  a non-linearizable one would answer Cantat's local-RF question negatively.
- `comm-of-z-n-times-torsion-group-splits` (+ `-proof`): Comm(Z^n × B) = GL_n(Q) × Comm(B) for torsion B
  with trivial FC-centre (e.g. Grigorchuk: GL_n(Q) × V(Grig)). Never f.g.
- Artifact `gq-gq-explicit-2-aut-comm-hosts.md`; 2.7 root Attempt 3.

**Needs.** none

**Dead.** RF automorphism hosts; linear Cremona copies; Z^n-thickened Röver commensurators; Comm(Z^n),
Comm(SL_n(Z)), com(F) (not f.g.). FW for SL_n(Q): impossible (countable non-f.g. ⇒ no FA, Serre).

**Sparks (free to adopt).**
- S1: is (Q,+) ≤ Aut(V)? (Aut(V_n) = bi-synchronizing transducer homeomorphisms, BCMNO.)
- S2: a f.g. branch/self-replicating Δ with f.g. Comm(Δ) ⊇ GL_n(Q)? (PGL_2(Q) ≤ Aut(T_{p+1}) ≤ Neretin.)
- S3: f.g. subgroups of com(F) omit Aff(Q) IF BCR's germ description holds (needs source check).
