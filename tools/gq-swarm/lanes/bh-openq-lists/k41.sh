cd /projects/standard/hsiehph/sauer354/openq-lists/ksrc
tr '\n' ' ' < 21tkt.tex | LC_ALL=C sed 's/  */ /g; s/\\bmp /\n/g' | LC_ALL=C grep -E '^\\textbf\{(\\zv )?21\.(41|140)\.' | cut -c1-1500
