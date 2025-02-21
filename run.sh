#!/bin/bash

theorem_list=(
  "theorem PExample {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) : 1 / (a + 2) + 1 / (b + 2) + 1 / (c + 2) ≤ 1 / (6 * sqrt (a * b) + c) + 1 / (6 * sqrt (b * c) + a) + 1 / (6 * sqrt (c * a) + b) := by sorry"
)


for theorem in "${theorem_list[@]}"
do

theorem_name=$(echo "$theorem" | grep -oP 'P[a-zA-Z0-9]+')
pkill -9 python > /dev/null 2>&1
pkill -9 lean > /dev/null 2>&1
mkdir -p "Results/$theorem_name"
python -u prove.py \
    --problem "$theorem" \
    --save_dir "Results/$theorem_name" \
    --log_level "INFO" \
    --num_threads 192 \
    --force_rebuild 1 \
    --oai_version "gpt-4o-mini" \
    --temperature 0.1 \
    --top_p 0.95 \
    --max_tokens 4096 \
    --focus_ops "d" \
    --norm_goal 1 \
    --rank_size 10 \
    --check_cycle 0 \
    --scale_limit 128 \
    --scale_equality 1 \
    --check_homogeneous 1 \
    --rewrite_length 5 \
    --rewrite_limit 1 \
    --init_test "auto" \
    --smt_config "{'smt_timeout': 5, 'smt_level': 0, 'smt_solvers': ['z3', 'cvc5', 'mplbt', 'mplrc', 'mmard', 'mmafi', 'sysol', 'syopt'], 'smt_update': True}" \
    --prover_vb 1 

  sleep 1
done



