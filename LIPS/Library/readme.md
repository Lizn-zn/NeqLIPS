## Include more tactics

#### 1. Add more rewriting tactics

The rewriting tactics are defined in `LIPS/Library/RewritingLib.json`. 
One can add more tactics like the following, and add the corresponding Lean tactic in `Neq/math/Math/Tactics.lean`.
```
"REWRITE_NAME": {
    "prompt": "LLM prompt",
    "tactic": "Lean 4 tactic name",
    "type": "rewrite_without_assumption | rewrite_with_assumption | rewrite_with_inequation",
    "sym_only": "whether only use symbolic rewriting"
}
```

#### 2. Add more scaling tactics
The scaling tactics are defined in `LIPS/Library/ScalingLib.json`. 
One can add more tactics like the following, and add the corresponding Lean lemma in `Neq/math/Math/NeqScales.lean`.
```
"LEMMA_NAME_VERSION_DIRECTION_VARS": {
    "input": "Lemma_Input",
    "output": "Lemma_Output",
    "type": "Direction",
    "var": ["Var_List"],
    "condition": ["Equality_Condition"]
}
```