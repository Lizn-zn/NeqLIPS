import os
import re
import json
from wrapt_timeout_decorator import timeout

from .cmds import *
from .tree import ProofTree

from ..logger_config import default_logger, setup_logger

"""_summary_
This module defines the LeanIO class, which is a wrapper for the Lean process, providing a proof env
It provides a set of methods to interact with the Lean process and manage the proof tree.

USAGE:

REPL have the following four kinds of response

{'messages': [
    {'severity': 'info', 
     'pos': {'line': 0, 'column': 0}, 
     'endPos': {'line': 0, 'column': 0}, 
     'data': 'Try this: ring_nf'}, 
    {'severity': 'error', 
     'pos': {'line': 0, 'column': 0}, 
     'endPos': {'line': 0, 'column': 0}, 
     'data': 'unsolved goals\nblablablabbla'}]}

"""

tac_starts = ['--', '{', '}', 'scale', 'llm_simplify', 'llm_rearrange', 'smt!']

class LeanIO(ProofTree):
    def __init__(self, math_dir="./math", repl_dir="./repl", force_rebuild=False, logger=None):
        """
        verbose: 0) no output; 1) print the essential process; 2) print more details
        """
        ProofTree.__init__(self)
        self.logger = logger or default_logger
        current_dir = os.path.abspath('.')
        self.logger.info(f'Working at directory path = {current_dir}')
        ## build Math
        self.MathDir = os.path.abspath(math_dir)
        lake_dir = os.path.join(self.MathDir, '.lake')
        if (not os.path.isdir(lake_dir)) or force_rebuild:
            msg = run_lake_build(self.MathDir, 'mathlib')
            self.logger.info(f"build mathlib: {msg}")
            msg = run_lake_build(self.MathDir, 'smt')
            self.logger.info(f"build smt: {msg}")
            msg = run_lake_build(self.MathDir, '')
            self.logger.info(f"build lean: {msg}")
        ## build REPL
        self.ReplDir = os.path.abspath(repl_dir)
        lake_dir = os.path.join(self.ReplDir, '.lake')
        if (not os.path.isdir(lake_dir)) or force_rebuild:
            run_lake_build(self.ReplDir, 'repl')
        ## initialize ProofEnv
        proc = run_env_build(self.MathDir, self.ReplDir, log_file=None)
        self.process = proc
        self.env = None
        self.logger.info(self.get_lean_version())

    def get_lean_version(self):
        return run_version_query()
    
    def build(self, cmd: str) -> int:
        """
        Build the proof environment
        if the new goal is generated, return the proof state index else return -1
        """
        obj = {'cmd': cmd}
        if self.env is not None:
            obj['env'] = self.env
        try:
            write_json(stdout=self.process.stdin, obj=obj)
            res = read_json(stdin=self.process.stdout)
        except json.JSONDecodeError:
            raise ValueError(f"Fail to parse the cmd: {obj}")
        self.env = res['env'] # update env
        prev_idx = self.get_node_idx(-1)
        # pre-check
        if "error" in str(res):
            self.logger.error(f"LeanIO may encounter some unknown error")
            self.logger.error(f"The cmd is {cmd}")
            self.logger.error(f"The response is {res}")
            raise ValueError(f"LeanIO may encounter some unknown error, please check the command {cmd}")
        if "sorries" in res: # start to build the tree
            sorries = res['sorries']
            if len(sorries) > 1:
                raise ValueError("The definition should not have multiple sorries")
            sorry = sorries[0]
            ps_idx = sorry['proofState']
            curr_idx = self.set_node_idx(ps_idx)
            goals = [sorry.get('goal', '')]
            self.create_node(cmd.replace("sorry", ""), 
                            identifier=curr_idx, 
                            parent=prev_idx, 
                            data={'tactic': cmd, 'goal': goals})
        else:
            ps_idx = -1
        return ps_idx
    
    def declare(self, cmd: str, env: int=-1, ps: int=-1) -> tuple[int, int]:
        """
        Specificy apply function for `suffices` and `have`
        """
        raise NotImplementedError("The declare function is not implemented")
    
    @timeout(30)
    def apply(self, cmd: str, ps: int) -> int:
        """
        Apply the tactic to the given proof state
        there are three cases in the response:
        1) failed: {'message': ''}
        2) forward: {'proofState': 1, 'messages': [{'severity': '', 'pos': {}, 'endPos': {}, 'data': ''},'goals': []}
        3) sorry: {'sorries': [{'goal': '', 'proofState': 1}], 'message': ''}
        """
        cmd = cmd.strip()
        prev_idx = self.get_node_idx(ps)
        obj = {'tactic': cmd, 'proofState': ps}  
        try:
            write_json(stdout=self.process.stdin, obj=obj)
            res = read_json(stdin=self.process.stdout)
        except json.JSONDecodeError as e:
            raise ValueError(f"Fail to parse the cmd: {obj}")
        # parse the result and define a new node
        message = res.get('message', '')
        messages = res.get('messages', [])
        msg = message + "\n" + str(messages)
        if 'proofState' in res:
            if "error" not in msg: # it refers to that tac achieves a forward step
                curr_ps = res['proofState']
                curr_idx = self.set_node_idx(curr_ps)
                goals = res.get('goals', []) # it returns a list
                self.create_node(cmd, 
                                identifier=curr_idx, 
                                parent=prev_idx, 
                                data={'tactic': cmd, 'goal': goals}) 
                response = {
                    'goals': res.get('goals', []),
                    'messages': msg
                }
                self.logger.info(f"Success to forward a step using `{cmd.strip()}` on ps {ps}, deriving new ps {curr_ps}")
            else:
                curr_ps = ps
                response = {
                    'messages': msg
                }
                self.logger.info(f"Fail to make any progress using `{cmd.strip()}` on ps {ps}")
        else:
            curr_ps = ps
            self.logger.error(f"Fail to parse the response {res} for running the cmd: {cmd}")
        return curr_ps
    
            
    def close(self) -> bool:
        self.process.stdin.close()
        self.process.stdout.close()
        self.process.terminate()
        self.process.wait()
        return True
        
# EOC of ProofEnv 