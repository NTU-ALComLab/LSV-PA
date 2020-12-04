#!/bin/bash

ref_cmd="lsv_print_pounate"
time_limit="300s"
pa_dir="lsv/pa2"
ref_dir="${pa_dir}/ref"
bench_dir="benchmarks"
bench_list=("${bench_dir}/random_control/arbiter.aig"
            "${bench_dir}/random_control/cavlc.aig"
            "${bench_dir}/random_control/ctrl.aig"
            "${bench_dir}/random_control/dec.aig"
            "${bench_dir}/random_control/i2c.aig"
            "${bench_dir}/random_control/int2float.aig"
            "${bench_dir}/random_control/mem_ctrl.aig"
            "${bench_dir}/random_control/priority.aig"
            "${bench_dir}/random_control/router.aig"
            "${bench_dir}/arithmetic/adder.aig"
            "${bench_dir}/arithmetic/bar.aig"
            "${bench_dir}/arithmetic/max.aig"
            "${bench_dir}/arithmetic/sin.aig")

rm src/ext-lsv/*.o src/ext-lsv/*.d
make -j8
rm -rf "${ref_dir}"
mkdir -p "${ref_dir}"
for bench in "${bench_list[@]}"; do
    echo "[INFO] Generating a reference output for ${bench} ..."
    bch_name=$(echo "${bench}" | awk -F "/" '{print $(NF)}' | sed -e 's/.aig$//')
    timeout "${time_limit}" ./abc -c "${ref_cmd}" "${bench}" > "${ref_dir}/${bch_name}.txt"
    if [ "$?" -ne 0 ]; then
        echo "  [ERROR] Timeout!"
    fi
done
