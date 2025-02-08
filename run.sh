#!/bin/bash

theorem_list=(
  "theorem P23a {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : 1 / sqrt (1 + 8 * a) + 1 / sqrt (1 + 8 * b) + 1 / sqrt (1 + 8 * c) ≤ 2 := by sorry"
  "theorem P46 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : (a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a) ≤ 1 := by sorry"
  "theorem P47 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : 1 ≤ a / sqrt (a ^ 2 + 8 * b * c) + b / sqrt (b ^ 2 + 8 * a * c) + c / sqrt (c ^ 2 + 8 * a * b) := by sorry"
  "theorem P48 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a + b + 2 * c) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) + (b + c + 2 * a) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) + (c + a + 2 * b) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) ≤ 8 := by sorry"
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
    --focus_ops "dm" \
    --norm_goal 1 \
    --rank_size 10 \
    --check_cycle 1 \
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



