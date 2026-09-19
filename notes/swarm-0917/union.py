import re,sys
for p in sys.argv[1:]:
    t=open(p).read()
    t=re.sub(r'<<<<<<< [^\n]*\n(.*?)=======\n(.*?)>>>>>>> [^\n]*\n', lambda m: m.group(1)+m.group(2), t, flags=re.S)
    open(p,'w').write(t)
