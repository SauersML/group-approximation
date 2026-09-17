"""Check the product construction of self-relaying-product-with-a-binary-identity over C_n.

Memory M = {0, 1} (sites g, g+1). A rule is (mu, d) with mu: L^2 -> L and d defined on patterns with active
output. We verify (D1), (D2), self-relaying and the type of tau x id exhaustively on all configurations of C_n.
Strictness is not tested: over C_n every injective automaton is surjective.
"""
import itertools
import random


def is_active(sym, z):
    return sym >= z


def check_donor_covering(mu, d, z, alphabet, n):
    """Return True iff (D1) and (D2) hold for all configurations on C_n."""
    for conf in itertools.product(alphabet, repeat=n):
        relayed = set()
        for g in range(n):
            u = (conf[g], conf[(g + 1) % n])
            if is_active(mu[u], z):
                h = (g + d[u]) % n
                if not is_active(conf[h], z):
                    return False  # D1
                relayed.add(h)
        for h in range(n):
            if is_active(conf[h], z) and h not in relayed:
                return False  # D2
    return True


def is_self_relaying(mu, d, z):
    return all(is_active(mu[u], z) and d[u] == 0 for u in mu if is_active(u[0], z))


def random_self_relaying(z, b, rng):
    L = list(range(z + b))
    mu, d = {}, {}
    for u in itertools.product(L, repeat=2):
        if is_active(u[0], z):
            mu[u], d[u] = rng.randrange(z, z + b), 0
        elif is_active(u[1], z) and rng.random() < 0.5:
            mu[u], d[u] = rng.randrange(z, z + b), 1
        else:
            mu[u] = rng.randrange(0, z)
    return L, mu, d


def product(mu, d, z, b):
    """tau x id with the donor map of the route; symbols (a, e), rest symbols (a, 0) with a < z listed first."""
    L = list(range(z + b))
    rest = [(a, 0) for a in range(z)]
    act = [(a, e) for a in L for e in (0, 1) if (a, e) not in rest]
    idx = {s: i for i, s in enumerate(rest + act)}
    sym = {i: s for s, i in idx.items()}
    zp = len(rest)
    mup, dp = {}, {}
    for pu in itertools.product(range(len(idx)), repeat=2):
        (a0, e0), (a1, _e1) = sym[pu[0]], sym[pu[1]]
        out = idx[(mu[(a0, a1)], e0)]
        mup[pu] = out
        if out >= zp:
            dp[pu] = 0 if pu[0] >= zp else d[(a0, a1)]
    return list(range(len(idx))), mup, dp, zp, len(act)


def main():
    rng = random.Random(20260917)
    for z, b in [(1, 1), (1, 2), (1, 4), (2, 2), (2, 4)]:
        for _trial in range(15):
            L, mu, d = random_self_relaying(z, b, rng)
            assert check_donor_covering(mu, d, z, L, 4)
            Lp, mup, dp, zp, bp = product(mu, d, z, b)
            assert zp == z and bp == 2 * b + z
            assert is_self_relaying(mup, dp, zp)
            n = 3 if len(Lp) > 8 else 4
            assert check_donor_covering(mup, dp, zp, Lp, n)
        print(f"type ({z},{b}) -> ({z},{2 * b + z}): product self-relaying and donor-covering, 15 rules")
    # Not self-relaying: the shift x(g+1) on {0,1} with donor g+1, type (1,1).
    L = [0, 1]
    mu = {u: u[1] for u in itertools.product(L, repeat=2)}
    d = {u: 1 for u in mu if u[1] == 1}
    assert check_donor_covering(mu, d, 1, L, 5) and not is_self_relaying(mu, d, 1)
    Lp, mup, dp, zp, bp = product(mu, d, 1, 1)
    assert not check_donor_covering(mup, dp, zp, Lp, 4)
    print("shift of type (1,1): inherited donor map of the product breaks (D2), as the Scope note says")


if __name__ == "__main__":
    main()
