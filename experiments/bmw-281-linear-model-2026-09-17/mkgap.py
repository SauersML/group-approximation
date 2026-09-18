import sys
from aut import perms, gapperm
name, n = sys.argv[1], int(sys.argv[2])
P = perms(name, n)
print('gens:=[' + ','.join(gapperm(P[a]) for a in sorted(P)) + '];')
