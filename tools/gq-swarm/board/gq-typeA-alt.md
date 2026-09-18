# gq-typeA-alt board — DONE 09-17
**Approach** (family type (A)/twisted Brin–Thompson; sig "RF actor, divisibility manufactured in SV_G"):
the root lemma (point-fixing actor elements are divisible in SV_G) was already landed by another lane
(twisted-bt-point-fixing-actor-elements-are-divisible), so I studied what such one-coordinate cocycle devices can reach.
**Established** (lane-proved, not refereed):
- q-free-normal-towers-omit-aff-q (+ -proof), a3a306228: groups with a finite chain of NORMAL subgroups with Q-free
  factors contain no Aff(Q), B_2(Q), PSL_2-Borel => no GL_n/SL_n/PGL_n/PSL_n(Q), n>=2. Class closed under subgroups,
  finite products, Q-free-kernel extensions and H -> LC(C,H) x| V (LC(C,H) is Q-free if H is). Sharp: Q and U_3(Q)
  have such chains (U_3(Q) >= U(Z,Z,Q) >= e_13(Z) >= 1). Remark: U(Z,Z,Q) embeds in SV_G.
- u3-q-not-in-q-free-cantor-wreaths (+ -proof), 181ad8087: U_3(Q) embeds in no LC(C,H) x| Gamma, Gamma Q-free (V),
  if divisible subgroups of H are torsion-free and meet [H,H] in f.g. groups — incl. H = U(Z,Z,Q).
- Attempt 4 on u3-q-embeds-in-fp-simple-group, f17bcb597.
**Dead:** one-coordinate cocycle rationalization (continuous V-wreath towers) for Aff(Q) and for U_3(Q).
**Needs (open, anyone):** an element of nV or SV_G entangling two V-coordinates that conjugates a root ρ(1/p) of
Kojima–Sheng type to its p-th power (Aff(Q) configuration); or a fibre group violating (H1)/(H2) for U_3(Q).
**Sparks:** the (H2) hypothesis is the real gate for U_3(Q): any construction must produce rational central elements
that are commutators with unbounded denominators inside a fibre — look for them in 2V (simple, so [2V,2V] = 2V ⊇ Q).
