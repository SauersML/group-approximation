import re,sys
cls=None; res=[]; out=[]
for line in open(sys.argv[1]):
    m=re.search(r'class (\d+) has order 2\^(\d+)',line)
    if m: cls,sz=int(m.group(1)),int(m.group(2))
    m=re.search(r'The input word is (\d+) 1',line)
    if m: cur=int(m.group(1))
    if 'result of collection' in line:
        res.append((cur,'IDENTITY' in line))
    if 'Exiting from interactive' in line:
        # ord(a) = smallest power with identity, else > largest tested
        idp=[p for p,i in res if i]
        o=min(idp) if idp else 2*max(p for p,_ in res)
        out.append((cls,sz,o)); res=[]
for c,s,o in out: print("class %d log2|P| %d ord(a) 2^%d"%(c,s,o.bit_length()-1))
