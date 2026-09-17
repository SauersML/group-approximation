def eig_vals(cp,w):
    """valuations of eigenvalues (Newton polygon) at monomial valuation w=(v(q),v(t))"""
    pts=[(k,min(w[0]*i+w[1]*j for (i,j) in cp[k])) for k in sorted(cp) if cp[k]]
    hull=[]
    for p in pts:
        while len(hull)>=2 and (hull[-1][1]-hull[-2][1])*(p[0]-hull[-2][0])>=(p[1]-hull[-2][1])*(hull[-1][0]-hull[-2][0]): hull.pop()
        hull.append(p)
    vals=[]
    for (k0,v0),(k1,v1) in zip(hull,hull[1:]):
        vals+= [-(v1-v0)/(k1-k0)]*(k1-k0)
    return sorted(vals)
def intervals(S):
    S=sorted(S); out=[]
    for s in S:
        if out and s==out[-1][1]+1: out[-1][1]=s
        else: out.append([s,s])
    return out
