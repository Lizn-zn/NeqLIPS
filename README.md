# Proving Olympiad Inequalities by Synergizing LLMs and Symbolic Reasoning

This is the official code for NeqLIPS, a powerful Olympiad Inequalities Prover.

![NeqLIPS](./figures/framework.png)

NeqLIPS first enumerates all possible scaling tactics using symbolic tools, and prompts LLMs to generate rewriting tactics. 
Then, it selects the best proof state by symbolic filtering and neural ranking.

## Quick Start

#### 1. Clone the repository

```
git clone https://github.com/Lizn-zn/NeqLIPS.git
```

#### 2. Install by Script

```
./Installation/install.sh
```

#### 3. Initialize the LLM interface

```
./NeSyCore/llm.py
```

#### 4. Run the Inequality Prover

```shell
python main.py --problem "theorem P14 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : 9 / (1 + a * b * c) ≤ (1 / a + 1 / b + 1 / c) * (1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c)) := by sorry"
```

#### Note:

1. If installation by script failed, please check the step-by-step readme in `./Installation` or build docker instead.
2. For more parameters in running or default parameters, see `run.sh`

## Proof Visualization



## TODO List
- [ ] README in `./Installation`
- [ ] Visualization of Proof Tree
- [ ] Alternative LLM DeepSeek instead of GPT-4
- [ ] Automation for rewrite tactics
- [ ] Convert SOS proof into Lean 4

## Questions and Bugs

To report a potential bug, please open an issue.

## License

This code repository is licensed under the MIT License.

## Citation

