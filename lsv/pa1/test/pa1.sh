
make -j16
./abc -c "read lsv/pa1/example.blif; strash; lsv_printmocut 3 2"
./abc -c "read lsv/pa1/example.blif; strash; lsv_printmocut 4 2"
./abc -c "read lsv/pa1/example.blif; strash; lsv_printmocut 5 2"
./abc -c "read lsv/pa1/example.blif; strash; lsv_printmocut 6 2"

./abc -c "read lsv/pa1/benchmarks/int2float.blif; strash; lsv_printmocut 3 2"
./abc -c "read lsv/pa1/benchmarks/int2float.blif; strash; lsv_printmocut 4 2"