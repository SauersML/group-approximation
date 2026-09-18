# bh-free-38 (free lane; seed: Nowak's Torelli lower-central quotients)
Direction: residual finiteness and BH for Q_{g,c} = Mod(S_g)/T_g[c+1] (g>=3, c>=2).
Landed (see commit in state/landed.log):
- torelli-lower-central-quotients-do-not-virtually-split (ESTABLISHED lane proof; Nowak Thm D + superrigidity).
- torelli-lower-central-quotients-are-not-residually-finite (+ -not-rf-proof): Hain line gives central Z; the virtual section's central extension is commensurable with a Deligne lattice over Sp_2g; Deligne ⇒ nontrivial finite residual. Trust surface: Borel H^2 range (g>=3), Hain, Margulis H^1 vanishing, Levi decomposition, Deligne via repo nodes.
- torelli-lower-central-quotients-satisfy-boone-higman (OPEN): WP open (reduction to J(c+1)/T[c+1]); all RF hosts excluded; hosts must contain a Deligne-type lattice over Sp_2g.
For bh-testcases / bh-kazhdan-inputs: this is a Deligne-lattice-containing hard test case; the Deligne-lattice host exclusions should transfer (unchecked).
