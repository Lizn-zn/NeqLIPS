from LIPS import parse_args
from LIPS import Prover
import datetime
from pprint import pprint

def print_separator(message: str):
    print("=" * 50 + f" {message} " + "=" * 50)

def generate(prover: Prover, problem: str):
    """
    Generate and process proof states for a given problem.
    
    Args:
        prover (Prover): The prover instance to use
        problem (str): The problem to prove
    """
    MAX_ITERATIONS = 200
    
    # Initialize problem
    print_separator("Prover Configs")
    print(f"{prover}\n")
    prover.set_problem(problem)
    
    # Main proof iteration loop
    for idx in range(MAX_ITERATIONS):
        # Prepare for new iteration
        prover.clean()
        prover.save_json()
        proof_state = prover.get_next()
        
        # Print iteration status
        print_separator(f"Iteration {idx}")
        print(f"Start time: {datetime.datetime.now()}")
        
        # Check if we've exhausted all states
        if proof_state == -1:
            print("No more proof states available")
            break
            
        # Probe the current state
        if idx > 0:
            smt_res, msg = prover.probe_state(proof_state)
        else:
            smt_res, msg = 1, ""
            
        # Process the state based on SMT result
        if smt_res <= 0:
            print(f"Failed to solve the problem: {msg}")
            states = []
        else:
            steps = prover.get_steps(proof_state)
            states = prover.get_state(proof_state, steps)
            
        # Check if proof is complete
        if states is None:
            return  # Proof completed successfully
            
        # Update and rank states
        prover.update_state(states)
        prover.rank_state()
    
    # Final symbolic check
    if not prover.close_by_sym():
        print("Failed to prove the problem")


if __name__ == "__main__":
    args = parse_args()
    pprint(vars(args), width=160)

    prover = Prover(args)
    problem = args.problem
    generate(prover, problem)

