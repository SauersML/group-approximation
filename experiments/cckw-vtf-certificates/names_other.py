import re
S = "/scratch.global/sauer354/ex/ex-hyperbolic-triangle-search/cckw/src"
ROW = re.compile(r"\$G_\{?(\d+)\}?\^\{(\d+),(\d+),(\d+)\}\$\s*&\s*\$(\d+)\$\s*&\s*(\S+)\s*&\s*(\S+)\s*&\s*(\d+)\s*&(.*?)&(.*?)&")
for tab in ["3_4_4", "4_4_4"]:
    rows = ROW.findall(open(S + "/table_" + tab + ".tex").read())
    q = [r for r in rows if r[5] == "?"]
    with open("names" + tab.replace("_", "") + "_q.txt", "w") as f:
        for r in q: f.write("G_%s^{%s,%s,%s}\n" % r[:4])
    print(tab, "rows", len(rows), "VTF?", len(q))
