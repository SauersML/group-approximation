import itertools, adt48
for sup in itertools.chain.from_iterable(itertools.combinations(range(-2, 3), r) for r in range(0, 3)):
    c = frozenset(sup)
    N = adt48.nucleus(c)
    kw = adt48.kernel_witness(c, 3)
    print("c=%-12s nucleus=%s kernel_witness=%s" % (sorted(c), "infinite/cap" if N is None else len(N), None if kw is None else (sorted(kw[0]), kw[1])), flush=True)
