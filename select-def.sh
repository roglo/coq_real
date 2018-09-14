cat $@ | egrep '(Theorem|Definition|Inductive|Fixpoint)' | sed -e 's/Theorem //; s/Definition //;s/Inductive //; s/Fixpoint //; s/ .*$//' | LC_ALL=C sort | LC_ALL=C uniq > def.txt
