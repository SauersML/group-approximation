"""Finite-precision check of the gadgets in research/twisted-brin-thompson-towers-pi-k-hardness-proof.md.

Points of the Cantor cube C^S are modelled by long finite binary strings, one per coordinate.
Every map used is a prefix-replacement map (possibly with a coordinate permutation), so it is
computed exactly as long as the strings are long enough.

Part 1 checks Lemma A on a toy actor: G = Sym(6) acting on S = {0..5}, with
K = permutations fixing r0 = 0 and r1 = 1, and s0 = 2.
Part 2 checks the base case of section 5 in 2V: gate gadgets, the circuit H, Claim 2, and the
multiplicative form p^-1 t_d^-1 H t_d p against s_base = 0C x C.
"""
import itertools
import random

random.seed(20260919)
LEN = 400


class El:
    """A word of primitive maps (f, finv), applied right to left. len(word) = letter count."""

    def __init__(self, f=None, finv=None, word=None):
        self.word = word if word is not None else [(f, finv)]

    @property
    def gen(self):
        return len(self.word)

    def __mul__(self, other):  # (self * other)(x) = self(other(x))
        return El(word=self.word + other.word)

    def inv(self):
        return El(word=[(b, a) for (a, b) in reversed(self.word)])

    def __call__(self, k):
        for f, _ in reversed(self.word):
            k = f(k)
        return k


IDENT = El(word=[])


def prod(els):
    out = IDENT
    for e in els:
        out = out * e
    return out


def power(e, j):
    if j < 0:
        return power(e.inv(), -j)
    return prod([e] * j)


def comm(a, b):
    return a * b * a.inv() * b.inv()


def coord_map(t, table):
    """Element of V acting on coordinate t by a finite prefix-replacement table."""
    inv_table = {v: u for u, v in table.items()}

    def app(tab):
        def f(k):
            x = k[t]
            for u, v in tab.items():
                if x.startswith(u):
                    k2 = list(k)
                    k2[t] = v + x[len(u):]
                    return tuple(k2)
            raise ValueError("table is not a partition")
        return f
    return El(app(table), app(inv_table))


def baker(r0, r1):
    def f(k):
        k2 = list(k)
        k2[r0] = k[r0][1:]
        k2[r1] = k[r0][0] + k[r1]
        return tuple(k2)

    def finv(k):
        k2 = list(k)
        k2[r0] = k[r1][0] + k[r0]
        k2[r1] = k[r1][1:]
        return tuple(k2)
    return El(f, finv)


def tau(g):
    """(tau_g kappa)(s) = kappa(g^-1 s); g is a tuple with g[s] = image of s."""
    ginv = [0] * len(g)
    for s, gs in enumerate(g):
        ginv[gs] = s

    def f(k):
        return tuple(k[ginv[s]] for s in range(len(g)))

    def finv(k):
        return tuple(k[g[s]] for s in range(len(g)))
    return El(f, finv)


def rand_bits(n):
    return "".join(random.choice("01") for _ in range(n))


def perm_mul(a, b):  # (ab)(s) = a(b(s))
    return tuple(a[b[s]] for s in range(len(a)))


def perm_inv(a):
    out = [0] * len(a)
    for s, x in enumerate(a):
        out[x] = s
    return tuple(out)


GAMMA = {"0": "00", "10": "01", "11": "1"}
NOT_T = {"0": "1", "1": "0"}


# ---------------------------------------------------------------- Part 1: Lemma A on Sym(6)
def controlled_twist(k, r0):
    tk, tki = tau(k), tau(perm_inv(k))

    def f(kap):
        return tk(kap) if kap[r0][0] == "1" else kap

    def finv(kap):
        return tki(kap) if kap[r0][0] == "1" else kap
    return El(f, finv)


def lemma_a_trial(n, samples=30):
    S, r0, r1, s0 = 6, 0, 1, 2
    sig = baker(r0, r1)

    def rand_K():
        rest = [2, 3, 4, 5]
        img = rest[:]
        random.shuffle(img)
        g = [0, 1, 0, 0, 0, 0]
        for a, b in zip(rest, img):
            g[a] = b
        return tuple(g)

    ks = [rand_K() for _ in range(n)]
    h, p = rand_K(), rand_K()
    Y = prod([power(sig, -(i)) * controlled_twist(ks[i], r0) * power(sig, i) for i in range(n)])
    Z = tau(p).inv() * Y.inv() * tau(h) * Y * tau(p)
    alpha, beta = coord_map(s0, NOT_T), coord_map(s0, GAMMA)
    w = comm(Z * alpha * Z.inv(), beta)
    bad = positives = 0
    for d in itertools.product("01", repeat=n):
        t = tuple(range(S))
        for i in range(n):
            if d[i] == "1":
                t = perm_mul(t, ks[i])
        g = perm_mul(perm_inv(p), perm_mul(perm_inv(t), perm_mul(h, perm_mul(t, p))))
        predicted = g[s0] == s0
        moved = False
        for _ in range(samples):
            kap = tuple(("".join(d) + rand_bits(LEN)) if s == r0 else rand_bits(LEN) for s in range(S))
            if w(kap) != kap:
                moved = True
                break
        bad += predicted != moved
        positives += predicted
    return bad, positives, 2 ** n


# ---------------------------------------------------------------- Part 2: base case in 2V
SIG2 = baker(0, 1)
SWAP = coord_map(0, {"00": "00", "01": "10", "10": "01", "11": "11"})
NOT = coord_map(0, NOT_T)
CNOT = coord_map(0, {"00": "00", "01": "01", "10": "11", "11": "10"})
TOF = coord_map(0, {a + b + c: a + b + (str(1 - int(c)) if a == b == "1" else c)
                    for a in "01" for b in "01" for c in "01"})
FIXED = {"NOT": (NOT, 1), "CNOT": (CNOT, 2), "TOF": (TOF, 3)}


def adj(j):  # exchange digits j, j+1 of x (1-indexed)
    return power(SIG2, -(j - 1)) * SWAP * power(SIG2, j - 1)


def gate(name, positions, M):
    """Fixed gate applied to digit positions (1-indexed, distinct) of x, via adjacent swaps."""
    el, r = FIXED[name]
    assert len(positions) == r
    arr = list(range(1, M + 1))  # arr[q-1] = wire currently at position q
    swaps = []
    for t, wire in enumerate(positions):
        q = arr.index(wire) + 1
        while q > t + 1:
            swaps.append(adj(q - 1))
            arr[q - 2], arr[q - 1] = arr[q - 1], arr[q - 2]
            q -= 1
    bring = prod(list(reversed(swaps)))  # first swap applied first
    return bring.inv() * el * bring


def random_circuit(n, m, g):
    """Gates of phi; signal ids: ('d',i), ('y',j), ('a',j)."""
    sigs = [("d", i) for i in range(n)] + [("y", j) for j in range(m)]
    gates = []
    for j in range(g):
        op = random.choice(["AND", "OR", "NOT"])
        if op == "NOT":
            gates.append((op, [random.choice(sigs)]))
        else:
            gates.append((op, random.sample(sigs, 2)))
        sigs.append(("a", j))
    return gates


def eval_phi(gates, d, y):
    val = {("d", i): d[i] for i in range(len(d))}
    val.update({("y", j): y[j] for j in range(len(y))})
    for j, (op, args) in enumerate(gates):
        v = [val[a] for a in args]
        val[("a", j)] = (v[0] & v[1]) if op == "AND" else (v[0] | v[1]) if op == "OR" else 1 - v[0]
    return val[("a", len(gates) - 1)]


def base_trial(n, m, g):
    """Layout: d at 1..n, b at n+1, ancillas at n+2..n+1+g, y at n+2+g..N."""
    N = n + 1 + g + m
    pos = {("d", i): 1 + i for i in range(n)}
    pos.update({("a", j): n + 2 + j for j in range(g)})
    pos.update({("y", j): n + 2 + g + j for j in range(m)})
    b = n + 1
    gates = random_circuit(n, m, g)
    rev = []
    for j, (op, args) in enumerate(gates):
        anc = pos[("a", j)]
        a = [pos[x] for x in args]
        if op == "AND":
            rev.append(gate("TOF", [a[0], a[1], anc], N))
        elif op == "OR":
            rev += [gate("NOT", [a[0]], N), gate("NOT", [a[1]], N), gate("TOF", [a[0], a[1], anc], N),
                    gate("NOT", [anc], N), gate("NOT", [a[0]], N), gate("NOT", [a[1]], N)]
        else:
            rev += [gate("CNOT", [a[0], anc], N), gate("NOT", [anc], N)]
    C = prod(list(reversed(rev)))  # rev[0] applied first
    o = pos[("a", g - 1)]
    T = gate("NOT", [o], N) * gate("CNOT", [o, b], N) * gate("NOT", [o], N)
    H = C.inv() * T * C
    bad = nsat = 0
    gamma = coord_map(0, GAMMA)
    p = power(gamma, n + g)
    flips = [power(SIG2, -i) * NOT * power(SIG2, i) for i in range(n)]
    for d in itertools.product([0, 1], repeat=n):
        ds = "".join(map(str, d))
        allsat = True
        for y in itertools.product([0, 1], repeat=m):
            ys = "".join(map(str, y))
            phi = eval_phi(gates, d, y)
            allsat &= bool(phi)
            for bit in "01":
                x = ds + bit + "0" * g + ys + rand_bits(LEN)
                z = rand_bits(LEN)
                out = H((x, z))
                want = ds + str(int(bit) ^ (1 - phi)) + "0" * g + ys + x[N:]
                bad += out != (want, z)
        # multiplicative form against s_base = 0C x C
        t = prod([flips[i] for i in range(n) if d[i] == 1])
        gd = p.inv() * t.inv() * H * t * p
        stab = True
        for y in itertools.product("01", repeat=m):
            for _ in range(2):
                inside = ("0" + "".join(y) + rand_bits(LEN), rand_bits(LEN))
                outside = ("1" + rand_bits(LEN), rand_bits(LEN))
                stab &= gd(inside)[0][0] == "0" and gd(outside)[0][0] == "1"
        bad += stab != allsat
        nsat += allsat
    return bad, nsat, H.gen, g * N * N


if __name__ == "__main__":
    tot = npos = nbox = 0
    for n in (2, 3, 4):
        for _ in range(5):
            bad, positives, boxes = lemma_a_trial(n)
            tot, npos, nbox = tot + bad, npos + positives, nbox + boxes
    print(f"Lemma A: {nbox} boxes over 15 random trials (n = 2..4), {npos} with g_d s0 = s0; mismatches: {tot}")
    for (n, m, g) in [(2, 2, 3), (2, 3, 5), (3, 2, 6), (3, 3, 8)]:
        tb = ts = 0
        for _ in range(4):
            bad, nsat, L, bound = base_trial(n, m, g)
            tb, ts = tb + bad, ts + nsat
        print(f"base n={n} m={m} g={g}: {4 * 2 ** n} values of d, {ts} with forall-y true; "
              f"mismatches={tb}  |H|={L} letters  g*N^2={bound}")

