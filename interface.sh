#!/bin/sh
grep -v '^Proof.*Qed' $* | sed -e '/^Proof/,/^Qed/d'
