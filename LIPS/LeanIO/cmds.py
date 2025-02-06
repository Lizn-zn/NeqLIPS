import subprocess
import json

def run_lake_build(directory, target_name, verbose=0):
    result = subprocess.run(
        ['lake', 'build', target_name],
        cwd=directory,
        text=True,
        capture_output=True
    )
    return result.stdout.strip()
        
def run_version_query():
    result = subprocess.run(
        ['lean', '--version'], 
        text=True, 
        capture_output=True, 
        check=True
    )
    return result.stdout.strip()
    
def run_env_build(math_dir, repl_dir, log_file):
    command = ['stdbuf', '-i0', '-o0', '-e0', 'lake', 'env', f'{repl_dir}/.lake/build/bin/repl']
    if log_file is not None:
        f = open(log_file, 'w')
    else:
        f = subprocess.DEVNULL
    process = subprocess.Popen(
        command, 
        stdout=subprocess.PIPE,
        stdin=subprocess.PIPE,
        stderr=f,
        encoding='utf-8',
        cwd=math_dir
    )
    return process

def read_json(stdin) -> dict:
    """
    
    """
    s = ""
    for _ in range(100):
        s = s + stdin.readline()
        try: 
            res = json.loads(s)
        except json.JSONDecodeError as e: 
            continue
        return res
    raise json.JSONDecodeError("The JSON object must be read in 100 lines", s, 100)

def write_json(stdout, obj):
    stdout.write(json.dumps(obj) + '\n\n')
    stdout.flush()