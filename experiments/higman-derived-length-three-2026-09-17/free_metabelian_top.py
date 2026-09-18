"""Two-variable detector for the one-sided example (see one_sided_example.py).

Choose F(p, s0) = S^(-p) on coset representatives (p, s0), 0 <= s0 < 2^p.  Since a.(p, s0) = (p-1, s0/2)
is again a representative, mu(a h) = mu(h) and F(a h) = S F(h), so f(a g) = S f(g) and f(c g) = t f(g).
Then Phi : A_m' -> C intertwines conjugation by a^m and c^m with S^m and t^m, and
Phi([c'^m, a'^m]) = t^-m (S^-m - 1)(1 + t + ... + t^(m-1)) != 0.
We check the equivariance and the formula numerically at t = 1.7, S = 2.3 for m = 1, 2.
"""
import mpmath as mp
import one_sided_example as E

SS = mp.mpf("2.3")

def Frep_two(rep):
    p, s0 = rep
    return SS ** (-p)

E.Frep = Frep_two

def main():
    TT = E.TT
    lines = []
    for _ in range(30):
        g = E.rand_g(8)
        assert E.close(E.f_g(E.gmul(E.ga, g)), SS * E.f_g(g))
        assert E.close(E.f_g(E.gmul(E.gc, g)), TT * E.f_g(g))
        gx, gbcx = E.gmul(g, E.gb), E.gmul(E.gmul(g, E.gb), E.gc)
        assert E.close(E.f_g(g), E.f_g(gx) + E.f_g(gbcx))
    lines.append("f(a g) = S f(g), f(c g) = t f(g), f(g) = f(gb) + f(gbc) on 30 random g")
    for m in (1, 2):
        am, cm = E.gpow_E(E.Ea, m), E.gpow_E(E.Ec, m)
        z = E.ecomm(cm, am)
        v = E.f_L(z[0])
        expect = TT ** (-m) * (SS ** (-m) - 1) * sum(TT ** i for i in range(m))
        assert E.close(v, expect), (m, v, expect)
        for i in range(3):
            for j in range(3):
                w = E.econj(E.econj(z, E.einv(E.gpow_E(am, i))), E.einv(E.gpow_E(cm, j)))
                assert E.close(E.f_L(w[0]), SS ** (m * i) * TT ** (m * j) * v)
        lines.append(f"m={m}: Phi(z) = t^-m (S^-m - 1)(1+..+t^(m-1)) and Phi(z^(alpha^-i gamma^-j)) = S^(mi) t^(mj) Phi(z), 0<=i,j<=2")
    print("\n".join(lines))

if __name__ == "__main__":
    main()
