/usr/bin/time ./pa1-ref -f run_benchmark.abc > ref.txt
/usr/bin/time ../../abc -f run_benchmark.abc > result.txt
diff -uwiB ref.txt result.txt