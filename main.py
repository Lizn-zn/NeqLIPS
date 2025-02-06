from LIPS import parse_args
from LIPS import Prover
import datetime
from colorama import Fore, Style
from pprint import pprint

# from collections import deque

import cProfile
import pstats
import io
from pstats import SortKey


def generate(prover: Prover, problem: str):
    print(Fore.GREEN + "=" * 50 + " Prover Configs " + "=" * 50 + "\n" + f"{prover} " + Style.RESET_ALL)
    prover.set_problem(problem)
    for idx in range(200):
        prover.clean()
        prover.save_json()
        proof_state = prover.get_next()
        print(Fore.GREEN + "=" * 50 + f" Iteration {idx} " + "=" * 50 + Style.RESET_ALL)
        print(Fore.GREEN + "Start time: " + f" {datetime.datetime.now()} " + Style.RESET_ALL)
        if proof_state == -1:
            print(Fore.RED + " No more proof states available " + Style.RESET_ALL)
            break
        if idx > 0:
            smt_res, msg = prover.probe_state(proof_state)
        else:
            smt_res = 1
        if smt_res <= 0:
            print(Fore.RED + f"Failed to solve the problem: {msg}" + Style.RESET_ALL)
            states = []
        else:
            steps = prover.get_steps(proof_state)
            states = prover.get_state(proof_state, steps)
        if states is None:
            return  # finish the proof
        else:
            prover.update_state(states)
            prover.rank_state()
    sos = prover.close_by_sym()
    if sos == False:
        print(Fore.RED + "Failed to prove the problem" + Style.RESET_ALL)


if __name__ == "__main__":
    args = parse_args()
    pprint(vars(args), width=160)

    pr = cProfile.Profile()
    pr.enable()

    prover = Prover(args)
    problem = args.problem
    generate(prover, problem)

    pr.disable()
    s = io.StringIO()
    sortby = SortKey.CUMULATIVE
    ps = pstats.Stats(pr, stream=s).sort_stats(sortby)
    ps.print_stats()
    print(s.getvalue())
