"""
AWPTSS (Anonymous Weakly Private Threshold Secret Sharing) Searcher

Description:
This script searches for t-out-of-n Anonymous Weakly Private Threshold Secret Sharing
(AWPTSS) schemes for a 1-bit secret over an alphabet of size q using the Z3 theorem prover.

In an AWPTSS scheme:
- Parties are anonymous (no identity distinction), so share sequences are treated as multisets.
- S0 and S1 are disjoint sets of n-multisets representing possible share distributions
  when the secret is 0 and 1, respectively.
- Reconstruction Requirement: Any multiset in S0 and any multiset in S1 can share at most
  t-1 elements. (If they shared t elements, those t shares could not reconstruct the secret).
- Weak Privacy Requirement: For any multiset in S0 and any of its (t-1)-sub-multisets,
  there must exist a multiset in S1 that contains this (t-1)-sub-multiset. (And vice-versa).

Usage:
    python awptss.py [-n <n>] [-t <t>] [-q <q>] [-o <output_directory>]

Arguments:
    -n, --n         Total number of shares (n) (default: 5)
    -t, --t         Threshold (t) (default: 4)
    -q, --q         Alphabet size (q) (default: 4)
    -o, --outdir    Directory to save the output file (default: current directory)

Example:
    python awptss.py                     # Runs with defaults: n=5, t=4, q=4
    python awptss.py -n 4 -t 3 -q 4 -o ./results
"""

import itertools
from collections import Counter
import argparse
import os
import sys

try:
    from z3 import Solver, Bool, Or, And, Not, Implies, sat, is_true
except ImportError:
    print("Error: The 'z3-solver' library is required.")
    print("Please install it using: pip install z3-solver")
    sys.exit(1)

def get_multisets(alphabet_size, k):
    """Generate all multisets of size k over the given alphabet size"""
    return list(itertools.combinations_with_replacement(range(alphabet_size), k))

def intersection_size(m1, m2):
    """Calculate the intersection size of two multisets"""
    return sum((Counter(m1) & Counter(m2)).values())

def get_subsets(m, k):
    """Get all unique sub-multisets of size k from multiset m"""
    return list(set(itertools.combinations(m, k)))

def log_print(msg, file_handle=None):
    """Print to terminal and file simultaneously"""
    print(msg)
    if file_handle:
        file_handle.write(str(msg) + "\n")

def log_print_list(items, header, file_handle=None, max_console_lines=10):
    """
    Print a list with a header. 
    Truncates console output if it exceeds max_console_lines, but writes fully to file.
    """
    print(f"\n{header}")
    if file_handle:
        file_handle.write(f"\n{header}\n")
        
    total_items = len(items)
    for idx, item in enumerate(items):
        line = f"  {item}"
        # Always write fully to file
        if file_handle:
            file_handle.write(line + "\n")
            
        # Truncate console output
        if idx < max_console_lines:
            print(line)
        elif idx == max_console_lines:
            print(f"  ... (Truncated. {total_items - max_console_lines} more items. See output file for full list)")

def extract_all_k_subsets(S, k):
    """Extract all sub-multisets of size k from a list of multisets S, deduplicate and sort"""
    res = set()
    for m in S:
        res.update(get_subsets(m, k))
    return sorted(list(res))

def search_awptss(q, n, t, file_handle=None):
    log_print(f"\n[*] Starting search for {t}-out-of-{n} AWPTSS (alphabet q={q})...", file_handle)
    multisets = get_multisets(q, n)
    num_m = len(multisets)
    
    # Variables: s0[i] == True means the i-th multiset belongs to S0
    s0 = [Bool(f"s0_{i}") for i in range(num_m)]
    s1 = [Bool(f"s1_{i}") for i in range(num_m)]
    
    solver = Solver()
    
    # Constraint 1: S0 and S1 are non-empty and disjoint
    solver.add(Or(s0))
    solver.add(Or(s1))
    for i in range(num_m):
        solver.add(Not(And(s0[i], s1[i])))
        
    # Constraint 2: Reconstruction requirement
    for i in range(num_m):
        for j in range(num_m):
            if intersection_size(multisets[i], multisets[j]) >= t:
                solver.add(Not(And(s0[i], s1[j])))
                
    # Constraint 3: Privacy requirement (Weak Privacy)
    for i in range(num_m):
        m_i = multisets[i]
        subsets = get_subsets(m_i, t - 1)
        
        for sub in subsets:
            contains_sub = [j for j in range(num_m) if intersection_size(multisets[j], sub) == len(sub)]
            solver.add(Implies(s0[i], Or([s1[j] for j in contains_sub])))
            solver.add(Implies(s1[i], Or([s0[j] for j in contains_sub])))
            
    # Solve and output
    if solver.check() == sat:
        log_print(f"[+] Successfully found a valid scheme for q={q}!", file_handle)
        model = solver.model()
        
        S0_res = [multisets[i] for i in range(num_m) if is_true(model[s0[i]])]
        S1_res = [multisets[i] for i in range(num_m) if is_true(model[s1[i]])]
        
        log_print_list(S0_res, f">>> S0 List (Total {len(S0_res)} multisets):", file_handle)
        log_print_list(S1_res, f">>> S1 List (Total {len(S1_res)} multisets):", file_handle)
        
        # Extract and print t-1 and t multisets
        S0_t_minus_1 = extract_all_k_subsets(S0_res, t - 1)
        S1_t_minus_1 = extract_all_k_subsets(S1_res, t - 1)
        S0_t = extract_all_k_subsets(S0_res, t)
        S1_t = extract_all_k_subsets(S1_res, t)
        
        log_print_list(S0_t_minus_1, f"=== All {t-1}-multisets in S0 (Total {len(S0_t_minus_1)}) ===", file_handle)
        log_print_list(S1_t_minus_1, f"=== All {t-1}-multisets in S1 (Total {len(S1_t_minus_1)}) ===", file_handle)
        log_print_list(S0_t, f"=== All {t}-multisets in S0 (Total {len(S0_t)}) ===", file_handle)
        log_print_list(S1_t, f"=== All {t}-multisets in S1 (Total {len(S1_t)}) ===", file_handle)
        
        # Automated assertions for visual inspection
        log_print(f"\n[*] Automated validation prompts (for visual inspection):", file_handle)
        is_p_s0_to_s1 = set(S0_t_minus_1).issubset(set(S1_t_minus_1))
        is_p_s1_to_s0 = set(S1_t_minus_1).issubset(set(S0_t_minus_1))
        log_print(f"    - Privacy: Are S0's {t-1}-multisets a subset of S1's? -> {is_p_s0_to_s1}", file_handle)
        log_print(f"    - Privacy: Are S1's {t-1}-multisets a subset of S0's? -> {is_p_s1_to_s0}", file_handle)
        
        intersection_t = set(S0_t).intersection(set(S1_t))
        log_print(f"    - Reconstruction: Intersection size of {t}-multisets in S0 and S1 should be 0 -> Actual size: {len(intersection_t)}", file_handle)
        if len(intersection_t) > 0:
            log_print(f"      [!] WARNING: Illegal intersection found: {intersection_t}", file_handle)

        return True
    else:
        log_print(f"[-] No solution found for q={q}.", file_handle)
        return False

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Search for Anonymous Weakly Private Threshold Secret Sharing (AWPTSS) schemes.",
                                     formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument("-n", type=int, default=5, help="Total number of shares (n) (default: 5)")
    parser.add_argument("-t", type=int, default=4, help="Threshold (t) (default: 4)")
    parser.add_argument("-q", type=int, default=4, help="Alphabet size (q) (default: 4)")
    parser.add_argument("-o", "--outdir", type=str, default=".", help="Directory to save the output file (default: current directory)")
    
    args = parser.parse_args()
    
    # Ensure output directory exists
    os.makedirs(args.outdir, exist_ok=True)
    
    output_filename = os.path.join(args.outdir, f"awptss_n{args.n}_t{args.t}_q{args.q}_results.txt")
    
    # Open file in write mode to redirect all output logs
    with open(output_filename, "w", encoding="utf-8") as f:
        log_print("=========================================", f)
        log_print(f"         AWPTSS Search Log (n={args.n}, t={args.t})", f)
        log_print("=========================================\n", f)
        
        search_awptss(q=args.q, n=args.n, t=args.t, file_handle=f)
            
    print(f"\n[i] All results and validation checks have been saved to: {output_filename}")