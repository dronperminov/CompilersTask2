mkdir -p outputs &&
gcc loop_invariants.c -L /usr/bin/qbe/lib -lqbe -o loop_invariants &&
./loop_invariants < tests/1.txt > outputs/1.txt &&
./loop_invariants < tests/2.txt > outputs/2.txt &&
./loop_invariants < tests/3.txt > outputs/3.txt &&
./loop_invariants < tests/4.txt > outputs/4.txt &&
./loop_invariants < tests/5.txt > outputs/5.txt &&
./loop_invariants < tests/6.txt > outputs/6.txt &&
./loop_invariants < tests/7.txt > outputs/7.txt &&
python3 test.py