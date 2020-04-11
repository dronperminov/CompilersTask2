all:
	gcc loop_invariants.c -L /usr/bin/qbe/lib -lqbe -o loop_invariants
# 	gcc loop_invariants.c -L /usr/bin/qbe/lib -lqbe -fsanitize=address -o loop_invariants