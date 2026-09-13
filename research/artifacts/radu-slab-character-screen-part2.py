# Screen 2: images mod p of A = <a,b,c> and H = <a,b,c,x,z>; descent of chi_c (c -> -1), chi_bc (b,c -> -1)
# on A and psi' on H; whether z (resp. y) lies in the image of A (resp. H).
import sys
# Run from a directory holding radu-slab-character-screen.py.
exec(open("radu-slab-character-screen.py").read().split("if __name__")[0])

def points(p):
    for m in range(1, p):
        if (2*m**4 - m**3 + 2*m**2 - m + 2) % p or (m + 1) % p == 0:
            continue
        for s in range(p):
            if (s*s + 4*(m*m + m + 1)) % p == 0:
                yield m, s

def run(p):
    for m, s in points(p):
        x = canon((1, 0, 0, p - 1), p); z = canon((0, 1, 1, 0), p)
        a = canon((0, m, 1, 0), p); y = canon((s, (-2*m) % p, 2, (-s) % p), p)
        b = mm(mm(z, a, p), z, p); c = mm(mm(y, b, p), y, p)
        Ac = closure([(a, 1), (b, 1), (c, -1)], p)
        Abc = closure([(a, 1), (b, -1), (c, -1)], p)
        Amats = {g for g, _ in Ac}
        H = closure([(a, 1), (b, 1), (c, -1), (x, -1), (z, -1)], p)
        Hm = {g for g, _ in H}
        print("p=%d m=%d s=%d |A|=%d chi_c_descends=%s chi_bc_descends=%s z_in_A=%s |H|=%d psi_descends=%s y_in_H=%s"
              % (p, m, s, len(Amats), len(Ac) == len(Amats), len(Abc) == len(Amats), z in Amats,
                 len(Hm), len(H) == len(Hm), y in Hm), flush=True)

if __name__ == "__main__":
    for p in [int(t) for t in sys.argv[1:]]:
        run(p)
    print("DONE")
