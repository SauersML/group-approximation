"""Triangular Harper sum K = Z + Z^* + X + X^* + T + T^*, T = e^(i pi/d) X Z = -D(1,1), W = 6, E = W - K >= 0.
For odd prime d: exact E_min = 6 - lambda_max(K); the Gaussian trial state psi(x) = exp(-pi(a - i b) x^2/d) on
representatives |x| <= (d-1)/2 with a = sqrt3/2, b = 1/2; its energy E(psi) against the Poisson main term
(pi/(a d))(1 + 2a^2 + b^2 + (1-b)^2) = 2 sqrt3 pi/d; and the resulting lower bound 4/E(psi) - 1 <= c(K)."""
import numpy as np, sys
for d in [int(a) for a in sys.argv[1:]] or [5, 7, 11, 13, 31, 61, 101, 211, 401]:
    w = np.exp(2j*np.pi/d); x = np.arange(d) - (d-1)//2
    X = np.roll(np.eye(d), 1, axis=0); Z = np.diag(w**(np.arange(d)))   # Z|x> = w^x |x>, depends on x mod d only
    T = np.exp(1j*np.pi/d) * X @ Z
    K = Z + Z.conj().T + X + X.conj().T + T + T.conj().T
    Emin = 6 - np.linalg.eigvalsh(K)[-1]
    a, b = np.sqrt(3)/2, 0.5
    psi = np.exp(-np.pi*(a - 1j*b)*x.astype(float)**2/d)            # index j <-> x = j - (d-1)/2, so Z = w^j = w^(x+(d-1)/2)
    # rebuild Z, X on the representative basis directly
    Zr = np.diag(w**x); Xr = np.zeros((d, d)); Xr[(np.arange(d)+1) % d, np.arange(d)] = 1
    Tr = np.exp(1j*np.pi/d) * Xr @ Zr
    Kr = Zr + Zr.conj().T + Xr + Xr.conj().T + Tr + Tr.conj().T
    psi = psi/np.linalg.norm(psi)
    Epsi = 6 - np.real(psi.conj() @ Kr @ psi)
    Emin_r = 6 - np.linalg.eigvalsh(Kr)[-1]
    main = 2*np.sqrt(3)*np.pi/d
    print(f"d={d}: Emin={Emin_r:.8f} (check {Emin:.8f})  E(psi)={Epsi:.8f}  2sqrt3 pi/d={main:.8f}  "
          f"E(psi)-main={Epsi-main:+.2e}  c={4/Emin_r-1:.4f}  4/E(psi)-1={4/Epsi-1:.4f}  2d/(sqrt3 pi)-1={2*d/(np.sqrt(3)*np.pi)-1:.4f}  d/pi={d/np.pi:.4f}", flush=True)
