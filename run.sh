#!/bin/bash

theorem_list=(
  "theorem P1 {a b c d : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (h : a * b + b * c + c * d + d * a = 1) : 1 / 3 ≤ a ^ 3 / (b + c + d) + b ^ 3 / (c + d + a) + c ^ 3 / (d + a + b) + d ^ 3 / (a + b + c) := by sorry",
  "theorem P2  {a b c d : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) : 2 / 3 ≤ a / (b + 2 * c + 3 * d) + b / (c + 2 * d + 3 * a) + c / (d + 2 * a + 3 * b) + d / (a + 2 * b + 3 * c) := by sorry",
  "theorem P3 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : 3 / 2 ≤ 1 / (c ^ 3 * (a + b)) + 1 / (a ^ 3 * (b + c)) + 1 / (b ^ 3 * (c + a)) := by sorry"
)


for theorem in "${theorem_list[@]}"
do

theorem_name=$(echo "$theorem" | grep -oP 'P[a-zA-Z0-9]+')
pkill -9 python > /dev/null 2>&1
pkill -9 lean > /dev/null 2>&1
mkdir -p "Results/$theorem_name"
python -u main.py \
    --problem "$theorem" \
    --save_dir "Results/$theorem_name" \
    --log_level "INFO" \
    --num_threads 192 \
    --force_rebuild 1 \
    --oai_version "gpt-4o" \
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
    --smt_config "{'smt_timeout': 15, 'smt_level': 0, 'smt_solvers': ['z3', 'cvc5', 'mplbt', 'mplrc', 'mmard', 'mmafi', 'sysol', 'syopt'], 'smt_update': True}" \
    --prover_vb 1 

  sleep 1
done



