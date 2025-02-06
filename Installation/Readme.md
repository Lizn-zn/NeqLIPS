
## Maple 2024 & Bottema

#### 1. Install maple2024
```shell
chmod +x Maple2020LinuxX64Installer.run
sudo ./Maple2020LinuxX64Installer.run
```

#### 2. Add path in `~/.bashrc`
```shell
export PATH=$PATH:/path/to/maple2024/bin
```

#### 3. Activate maple 2024 
Please refer to `readme.txt` in `./medicine`

#### 4. Prove inequalities using Bottema. 
For example, you can run the following command in Maple
```maple
read "./Bottema/bottema.mpl";
xprove(a^2+b^2>=2*a*b, [a>=0, b>=0]);
```

## Wolfram Mathematica

#### Install guidance 
[How do I set up Wolfram desktop products on Linux?](https://support.wolfram.com/65817)

#### 1. Copy your `mathpass` file to the same directory on the file server as the installer files.

#### 2. Install MMA
```shell
sudo sh Wolfram_14.1.0_LIN.sh 
```


## MT-Solve 

#### 1. Install PySMT (Bottema version) 
```shell
pip install git+https://github.com/Lizn-zn/pysmt.git@Bottema
```
#### 2. Install SMT solver 
using `pip` or `pysmt-install`, e.g.,
```shell
pip install cvc5
pysmt-install --msat
```
#### 3. Install MT-Solver
mt-Solver combines SMT solvers and other symbolic solvers (e.g. sympy solve, maple, mathematica).
```shell
pip install --force-reinstall git+https://github.com/Lizn-zn/MT-Solver.git
```
#### 4. Use `mtsolve`
Solve problem in smt-lib format:
```shell
mtsolve --fpath ./smt_test/case1.smt --z3 "--timeout 5" --bottema "--timeout 5"
```

## Lean-smt

#### 1. Add this line in lakefile.lean
```shell
require smt from git "https://github.com/Lizn-zn/lean-smt" @ "neq_dev"
```
#### 2. Prove by smt tactic, e.g.,
```
import Smt
def is_in_interval (x : ℝ) : Prop := x > 1 ∧ x < 6
theorem solution_to_inequality (x : ℝ) : x^2 - 7*x + 6 < 0 → is_in_interval x :=
    by smt [is_in_interval] (timeout := 30)
```

## Lean-REPL

#### 1. Clone the lean-repl
```
git clone git@github.com:leanprover-community/repl.git
```

#### 2.use `lean_interact.init` to initialize the lean environment, build the mathlib, and initialize `repl`.
```python
import lean_interface.lean_interact as LeanIO
LeanIO.init()
```
