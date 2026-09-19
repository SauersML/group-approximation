"""Closed form of the B-action on the Bass-Serre tree T_B of Gamma(3,m), m = 2^e.
A vertex of T_B at distance L from v = L1 is a word a^x1 c^x2 a^x3 c^x4 ... (x1 in Z/m, others nonzero).
With T = 3^-1 mod m, J_i = x1+x3+...+x_(2i-1), K_i = x2+x4+...+x_(2i):
   b^u : x_(2i)   -> x_(2i)   * T^(u 3^J_i)       (odd coordinates fixed)
   d^u : x_(2i-1) -> x_(2i-1) * T^(u 3^K_(i-1))   (even coordinates fixed)
   a   : x1 -> x1 + 1
This is the push rules b^q a^j = a^j b^(q 3^j), b^q c^k = c^(k T^q) b^q, d^q a^j = a^(j T^q) d^q,
d^q c^k = c^k d^(q 3^k) iterated along the word."""
def make(e):
    m = 2**e; T = pow(3, -1, m)
    def bu(u, x):
        x = list(x); J = 0
        for i in range(len(x)):
            if i % 2 == 0: J += x[i]
            else: x[i] = x[i] * pow(T, (u * pow(3, J % m, m)) % m, m) % m
        return tuple(x)
    def du(u, x):
        x = list(x); K = 0
        for i in range(len(x)):
            if i % 2 == 1: K += x[i]
            else: x[i] = x[i] * pow(T, (u * pow(3, K % m, m)) % m, m) % m
        return tuple(x)
    def a(x):
        return ((x[0] + 1) % (2**e),) + tuple(x[1:])
    return m, T, bu, du, a
