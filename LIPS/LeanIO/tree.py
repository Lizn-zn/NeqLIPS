from treelib import Tree, Node
import re

class ProofTree(Tree):
    def __init__(self):
        super().__init__()
        self.count = 0 # number of nodes
        self.ps2node = {} # ps_id -> node.identifier
        self.node2ps = {} # node.identifier -> ps_id

    def has_root(self):
        return self.root

    def get_rev_node_idx(self, node_idx: int) -> int:
        """
        Get the proof state idx for the given node index
        """
        return self.node2ps.get(node_idx, None)
        
    def get_node_idx(self, ps_idx: int) -> int:
        """
        Get the node index for the given proof state index
        """
        return self.ps2node.get(ps_idx, None)
    
    def get_node(self, node_idx: int) -> Node:
        """
        Get the node for the given node index
        """
        for node in self.all_nodes_itr():
            if node.identifier == node_idx:
                return node
        return None
    
    def set_node_idx(self, ps_idx: int) -> int:
        """
        Set the node index for the given proof state index
        """
        new_node_idx = self.count
        self.ps2node[ps_idx] = new_node_idx
        self.node2ps[new_node_idx] = ps_idx
        self.count += 1
        return new_node_idx

    def get_proof_tree(self, ps_idx: int = None) -> Tree:
        """
        Get the proof tree start from the given proof state index
        """
        node_idx = self.ps2node.get(ps_idx, None)
        if node_idx is not None:
            raise NotImplementedError("The proof subtree is not implemented")
        else:
            return self
        
    def get_steps(self, env, ps) -> int:
        """
        TODO: get all steps
        """
        # idx = self._get_node_idx(env, ps)
        # if idx is None:
        #     raise ValueError(f"Node {env} {ps} not found in the tree")
        # else:
        #     node = self._get_node(idx)
        #     node_tactic = node.data['tactic']
        #     steps = []
        #     while True:
        #         if "theorem" in node_tactic:
        #             break
        #         else:
        #             steps.append(node_tactic)
        #         node = self.parent(node.identifier)
        #         node_tactic = node.data['tactic']
        #     return steps
        raise NotImplementedError("The get steps is not implemented")
        
    def get_trace(self, ps_idx: int) -> list[str]:
        """
        Get the proof trace from the root to the given proof state index
        """
        node_idx = self.ps2node[ps_idx]
        if node_idx is None:
            raise ValueError(f"Node {ps_idx} not found in the tree")
        else:
            path_to_root = []
            node = self.get_node(node_idx)
            while node:
                path_to_root.append(node.tag)
                node = self.parent(node.identifier)
            return reversed(path_to_root)

    def print_trace(self, ps_idx: int) -> str:
        """
        Print the proof trace from the root to the given proof state index
        """
        traces = self.get_trace(ps_idx)
        return "\n  ".join(traces)
       
    def get_trace_idx(self, ps_idx: int) -> list[int]:
        """
        Get the proof trace indices from the root to the given proof state index
        """
        node_idx = self.ps2node[ps_idx]
        if node_idx is None:
            raise ValueError(f"Node {ps_idx} not found in the tree")
        else:
            path_to_root = []
            node = self.get_node(node_idx)
            while node:
                path_to_root.append(node.identifier)
                node = self.parent(node.identifier)
            return [p for p in reversed(path_to_root)]
        
    def remove_step(self, ps_idx: int) -> None:
        """
        Remove the node of the given proof state index
        """
        node_idx = self.ps2node[ps_idx]
        self.remove_node(node_idx)
    
    def exist_step(self, ps_idx: int) -> bool:
        """
        Check if the given proof state index exists in the tree
        """
        return self.get_node(ps_idx) is not None
        
    def remove_proof(self, ps_idx: int) -> int:
        """
        Remove the proof tree start from the given proof state index
        return the number of nodes removed
        """
        node_idx = self.ps2node[ps_idx]
        node = self.get_node(node_idx)
        num_removed = 0
        for c in self.children(node.identifier):
            num_removed += self.remove_node(c.identifier)
        return num_removed

    def print_proof(self, ps_idx: int) -> str:
        """
        Print the proof tree start from the given proof state
        """
        self.reduce_proof()
        node_idx = self.ps2node[ps_idx]
        if node_idx is not None:
            raise NotImplementedError("The proof subtree is not implemented")
        else:
            tree_str = ""
            root = self.get_node(self.root)
            # bfs the tree
            ind = 0 # intend level
            stack = [(root, ind)]
            while stack:
                node, ind = stack.pop()
                node_proof = node.tag.strip()
                tree_str += f"{ind*'  '}{node_proof}\n"
                if node_proof.endswith("by"):
                    ind = ind + 1
                for c in reversed(self.children(node.identifier)):
                    stack.append((c, ind))
            return tree_str
    
    def get_goals(self, ps_idx: int) -> list[str]:
        """
        Get the goals which are the children of the given proof state index
        """
        goals = []
        # only scan the leaf nodes start from start_idx
        start_idx = self.ps2node.get(ps_idx, None)
        if start_idx is None:
            start_idx = 0
        node = self.get_node(start_idx)
        goal = node.data.get("goal", "")
        if goal == "":
            return []
        else:
            for g in goal:
                g = g.split('⊢', 1)
                g = g[0] + '⊢' + re.sub(r'\s*\n\s*', ' ', g[1])
                goals.append(g)
        return goals    
          
    def reduce_proof(self):
        # reduce the repulicate node according to data
        # data_nodes = {} # data -> node_id
        # to_remove = []
        # for node in self.all_nodes_itr():
        #     node_data = ";".join(node.data.get('goal', []))
        #     node_tag = node.tag
        #     if node.is_root() or node.is_leaf() or node_data == "": # skip the leaf or root
        #         continue
        #     elif node_tag != "placeholder": # skip the Unproved placeholder
        #         data_nodes[node_data] = node.identifier                
        #     else:
        #         for c in self.children(node.identifier): # move children to the parent
        #             self.move_node(c.identifier, self.parent(node.identifier).identifier)
        #         to_remove.append(node.identifier)
        # for node_id in to_remove:
        #     self.remove_node(node_id)
        pass


    def to_dict(self, nid=None, golden_path=[]):
        """Transform the whole tree into a dict (hook the original implementation)
            golden_path: the path from the root to the finish state
            nid: the node id
        """
        nid = self.root if (nid is None) else nid
        is_golden = True if nid in golden_path else False
        tree_dict = {"name": '\n'.join(self[nid].data['goal']), "children": []}
        tree_dict["data"] = {**self[nid].data, "is_golden": is_golden}
        if self[nid].expanded:
            for elem in self.children(nid):
                tree_dict["children"].append(
                    self.to_dict(elem.identifier, golden_path))
            return tree_dict