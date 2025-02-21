import argparse
  
def parse_args():  
    """
    Parse the arguments for the main function
    """
    argparser = argparse.ArgumentParser(description="Process theorem statement and values.")
    argparser.add_argument("--problem", default="", type=str, help="Input theorem statement")
    argparser.add_argument("--save_dir", default="Results", type=str, help="Saved path for output file")
    argparser.add_argument("--log_level", default="INFO", type=str, choices=["INFO", "DEBUG", "WARNING", "ERROR"], help="Log level for output")
    argparser.add_argument("--num_threads", default=96, type=int, help="Number of threads")
    ### LeanIO params
    argparser.add_argument("--math_dir", default="./Neq/math", type=str, help="Math directory for LeanIO")
    argparser.add_argument("--repl_dir", default="./Neq/repl", type=str, help="Repl directory for LeanIO")
    argparser.add_argument("--force_rebuild", default=1, choices=[0, 1], type=int, help="Force rebuild for LeanIO")
    # Problem params
    argparser.add_argument("--check_cycle", default=0, choices=[0,1], type=int, help="Whether using the cycle check, filtering out non-cycle states")
    argparser.add_argument("--check_homogeneous", default=1, choices=[0, 1], type=int, help="Whether to make the problem homogeneous previously")
    # Ranker params
    argparser.add_argument("--focus_ops", default="dm", type=str, help="Operator encouraged for the problem, e.g., d+")
    argparser.add_argument("--norm_goal", default=0, choices=[0,1], type=int, help="Whether to normalize the goal")
    argparser.add_argument("--rank_size", default=10, type=int, help="Filter size for the Ranker")
    # Scaler params
    argparser.add_argument("--scale_limit", default=128, type=int, help="Size limit for each pattern match of given premise, -1 means unlimited")
    argparser.add_argument("--scale_equality", default=0, choices=[0,1], type=int, help="Whether using the equality check")
    argparser.add_argument("--init_test", default="auto", type=str, help="Values dictionary as a string or auto")
    # Rewriter params
    argparser.add_argument("--rewrite_limit", default=1, type=int, help="Number of candidates when llm rewriting")
    argparser.add_argument("--rewrite_length", default=5, type=int, help="Maximum subsequent rewrite steps for the problem")
    argparser.add_argument("--sym_rewrite", default=0, choices=[0,1], type=int, help="Whether only using the symbolic rewrite")
    # params for the smt solver
    argparser.add_argument("--smt_config", default="", type=str, help="SMT solvers for accepting the tactic")
    # LLM params
    argparser.add_argument("--oai_version", default="gpt-4", type=str, help="API for LLM")
    argparser.add_argument("--temperature", default=0.7, type=float, help="Temperature for LLM sampling")
    argparser.add_argument("--top_p", default=0.95, type=float, help="Top p for LLM sampling")
    argparser.add_argument("--max_tokens", default=4096, type=int, help="Max tokens for LLM sampling")
    # verbose mode
    argparser.add_argument("--prover_vb", default=0, choices=[0, 1, 2], type=int, help="Set verbosity for Prover")
    args = argparser.parse_args()
    return args
