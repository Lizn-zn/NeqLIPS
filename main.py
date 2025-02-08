from LIPS import parse_args
from LIPS import Prover
import datetime
from pprint import pprint

# from collections import deque

import cProfile
import pstats
import io
from pstats import SortKey


def generate(prover: Prover, problem: str):
    print("=" * 50 + " Prover Configs " + "=" * 50 + "\n" + f"{prover} ")
    prover.set_problem(problem)
    for idx in range(200):
        prover.clean()
        prover.save_json()
        proof_state = prover.get_next()
        print("=" * 50 + f" Iteration {idx} " + "=" * 50)
        print("Start time: " + f" {datetime.datetime.now()} ")
        if proof_state == -1:
            print(" No more proof states available ")
            break
        if idx > 0:
            smt_res, msg = prover.probe_state(proof_state)
        else:
            smt_res = 1
        if smt_res <= 0:
            print(f"Failed to solve the problem: {msg}")
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
        print("Failed to prove the problem")


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
