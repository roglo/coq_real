for i in $(cat def.txt); do grep -w $i *.v | echo "$(wc -l) $i"; done | LC_ALL=C sort -n
