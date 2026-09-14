---
rg: 2
id: heisenberg-group-lies-in-no-z-subshift-elementary-group-proof
kind: route
title: The Heisenberg centre is quadratically distorted, and crossed-product linear groups have no distortion
target: heisenberg-group-lies-in-no-z-subshift-elementary-group
requires:
  - subshift-crossed-product-gl-has-no-distorted-elements
artifacts:
  - research/artifacts/sk-sl3z-bandwidth-distortion-obstruction-2026-09-13.md
---

1. **Distortion in H.** In H = ⟨a,b | [a,c],[b,c]⟩ with c = [a,b], c is central of infinite order (H ≅ the upper unitriangular integer 3×3 matrices, and c ↦ e_13(1)).
   - Since c is central, [a^n,b^n] = c^{n²}.
   - For n² ≤ N < (n+1)², c^N = [a^n,b^n]c^{N−n²} with N−n² ≤ 2n. So |c^N|_{\{a,b\}} ≤ 4n + 4·2n ≤ 12√N, and lim|c^N|/N = 0.
2. **No embedding.** An injective Γ ≤ GL_m(LC(X,F_q)⋊Z) with Γ ≅ H would have c of infinite order and stable length 0. This contradicts `subshift-crossed-product-gl-has-no-distorted-elements`: take S = the images of a^{±1}, b^{±1}, whose entries involve boundedly many powers of u.
3. **G_X.** G_X ≤ GL_3(LC(X,F_2)⋊Z), so H lies in no G_X.
4. **Overgroups.** SL_n(Z) ⊇ H for n ≥ 3. In BS(1,2) = ⟨a,t | tat^{-1} = a²⟩, a^{2^k} = t^k a t^{-k} has length ≤ 2k+1, so a is distorted. Overgroups inherit the obstruction. ∎
