# automaton groups on ternary tree; state a: a(x w) = out[a][x] sec[a][x](w)
import itertools
AUT = {
 '281': ({0:(0,1,2),1:(0,2,1),2:(0,2,1),3:(1,0,2)}, {0:(1,1,1),1:(0,2,2),2:(2,0,0),3:(3,3,3)}),
 '332V': ({0:(0,1,2),1:(0,2,1),2:(0,2,1),3:(1,0,2)}, {0:(1,1,1),1:(2,0,0),2:(0,2,2),3:(3,3,3)}),
 '332H': ({0:(0,2,1),1:(0,1,2),2:(0,1,2),3:(1,0,2)}, {0:(1,1,1),1:(0,2,2),2:(2,0,0),3:(3,3,3)}),
 '193V': ({0:(0,1,2),1:(0,1,2),2:(1,0,2),3:(0,2,1)}, {0:(0,0,2),1:(2,2,0),2:(1,1,1),3:(3,3,3)}),
 '193H': ({0:(0,1,2),1:(0,1,2),2:(0,2,1),3:(1,0,2)}, {0:(0,0,3),1:(3,3,0),2:(2,2,2),3:(1,1,1)}),
}
def perms(name, n):
    out, sec = AUT[name]
    # leaves: words of length n, index = sum x_i 3^(n-1-i) (first letter most significant)
    P = {}
    def img(a, w):
        r = []
        for x in w:
            r.append(out[a][x]); a = sec[a][x]
        return tuple(r)
    words = list(itertools.product(range(3), repeat=n))
    idx = {w:i for i,w in enumerate(words)}
    return {a: [idx[img(a,w)] for w in words] for a in out}
def gapperm(p):
    return 'PermList([' + ','.join(str(i+1) for i in p) + '])'
