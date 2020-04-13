test:
	./make_test.sh

build loop_invariants:
	gcc loop_invariants.c -L /usr/bin/qbe/lib -lqbe -o loop_invariants

sanitize:
	gcc loop_invariants.c -L /usr/bin/qbe/lib -lqbe -fsanitize=address -o loop_invariants

1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20: loop_invariants
	./loop_invariants < tests/$@.txt

.PHONY: 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 sanitize build test
