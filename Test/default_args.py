import argparse

def parse_args():
    """
    Return a default or mock argument object for testing purposes.
    """
    # 直接返回一个模拟的 Namespace 对象，不解析命令行
    return argparse.Namespace(
        problem="",
        num_threads=92,
        init_test="auto",
        check_homogeneous=1,
        scale_limit=-1,
        rewrite_limit=1,
        sym_rewrite=0,
        norm_goal=1,
        smt_config="{'smt_timeout': 15, 'smt_level': 0, 'smt_solvers': ['z3', 'cvc5', 'mplbt', 'mplrc', 'mmard', 'mmafi', 'sysol', 'syopt'], 'smt_update': True}",
        save_dir="Results/Test",
        log_level="debug",
        math_dir="./Neq/math",
        repl_dir="./Neq/repl",
        log_file=None,
        force_rebuild=0,
        focus_ops="+",
        rank_size=10,
        scale_equality=0,
        check_cycle=1,
        oai_version="gpt-4",
        temperature=0.7,
        top_p=0.95,
        max_tokens=4096,
        prover_vb=0,
        leanio_vb=0,
        ranker_vb=0,
        rewriter_vb=0,
        scaler_vb=0
    )