mkdir -p outputs &&
gcc loop_invariants.c -L /usr/bin/qbe/lib -lqbe -o loop_invariants &&
./loop_invariants < tests/1.txt > outputs/1.txt &&
./loop_invariants < tests/2.txt > outputs/2.txt &&
./loop_invariants < tests/3.txt > outputs/3.txt &&
./loop_invariants < tests/4.txt > outputs/4.txt &&
./loop_invariants < tests/5.txt > outputs/5.txt &&
./loop_invariants < tests/6.txt > outputs/6.txt &&
./loop_invariants < tests/7.txt > outputs/7.txt &&
./loop_invariants < tests/8.txt > outputs/8.txt &&
./loop_invariants < tests/9.txt > outputs/9.txt &&
./loop_invariants < tests/10.txt > outputs/10.txt &&
./loop_invariants < tests/11.txt > outputs/11.txt &&
./loop_invariants < tests/12.txt > outputs/12.txt &&
./loop_invariants < tests/13.txt > outputs/13.txt &&
./loop_invariants < tests/14.txt > outputs/14.txt &&
python3 test.py
