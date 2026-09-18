# Free-group identities used in higman-solvable-by-metabelian-edge-collapse-proof, Step 2.
# Conventions: x^y = y^-1 x y, Comm(x,y) = x^-1 y^-1 x y (GAP's Comm agrees).
F := FreeGroup("g","z","w","h","u");; g:=F.1;; z:=F.2;; w:=F.3;; h:=F.4;; u:=F.5;;
# (1) (g z)^2 = g^2 * z^g * z   [phi(gamma^alpha) = (gamma z)^2]
Print("identity1 ", (g*z)^2 = g^2 * z^g * z, "\n");
# (2) with k := h*u^-1:  Comm(w,k) = Comm(w,u^-1) * Comm(w,h)^(u^-1)
k := h*u^-1;;
Print("identity2 ", Comm(w,k) = Comm(w,u^-1) * Comm(w,h)^(u^-1), "\n");
QUIT;
