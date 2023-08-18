# SAT verifier of GoL preimage gadgets
# All patterns are assumed to be rectangular, positive y-axis points south

from pysat.solvers import Glucose4
import math
import os.path
import argparse
from pattern_basics import neighborhood

# SAT encodings
import bisector
import sort_network
import totalizer

ENCODING = None


def gol_preim_inst(pattern):
    "SAT instance for Game of Life preimage"
    cells = set(nbr for vec in pattern for nbr in neighborhood(vec))
    variables = {vec : ENCODING.gen_var() for vec in cells}
    clauses = [clause
               for (vec, value) in pattern.items()
               for clause in ENCODING.local_preimage([variables[nbr]
                                                      for nbr in neighborhood(vec)],
                                                     min(value, 1))]

    ENCODING.reset_var()
    return clauses, variables
    

def find_wires(pattern):
    "Locate the NW corner of a wire in operating phase on each border of the pattern (or None)"
    min_x = min_y = math.inf
    max_x = max_y = -math.inf
    for (x,y) in pattern:
        min_x = min(min_x, x)
        max_x = max(max_x, x)
        min_y = min(min_y, y)
        max_y = max(max_y, y)
    # west and east wires
    w = e = None
    for y in range(min_y, max_y):
        if all(pattern[x, y+j] > 0 for x in [0,1] for j in [0,1]):
            # found wire, now need to find operating phase
            for x in range(3):
                if all(pattern[x+i, y+j] in [1,3] for i in [0,1] for j in [0,1]):
                    w = (x,y)
        if all(pattern[x, y+j] > 0 for x in [max_x-1,max_x] for j in [0,1]):
            # found wire, now need to find operating phase
            for x in reversed(range(max_x-3, max_x)):
                if all(pattern[x+i, y+j] in [1,3] for i in [0,1] for j in [0,1]):
                    e = (x,y)
    # north and south wires
    n = s = None
    for x in range(min_x, max_x):
        if all(pattern[x+i, y] > 0 for i in [0,1] for y in [0,1]):
            # found wire, now need to find operating phase
            for y in range(3):
                if all(pattern[x+i, y+j] in [1,3] for i in [0,1] for j in [0,1]):
                    n = (x,y)
        if all(pattern[x+i, y] > 0 for i in [0,1] for y in [max_y-1,max_y]):
            # found wire, now need to find operating phase
            for y in reversed(range(max_y-3, max_y)):
                if all(pattern[x+i, y+j] in [1,3] for i in [0,1] for j in [0,1]):
                    s = (x,y)
    return (e,n,w,s)

#def inner_border(pattern):
#    "Set of cells at border"
#    return set(vec for vec in pattern
#               if any(nbr not in pattern for nbr in neighborhood(vec)))

def thick_border(pattern, wires=None):
    "Set of cells at or right outside border, but not near wires"
    min_x = min_y = math.inf
    max_x = max_y = -math.inf
    for (x,y) in pattern:
        min_x = min(min_x, x)
        max_x = max(max_x, x)
        min_y = min(min_y, y)
        max_y = max(max_y, y)
    excepted = set()
    if wires is not None:
        e, n, w, s = wires
        if e is not None:
            for j in [-1,0,1,2]:
                for x in [max_x, max_x+1]:
                    excepted.add((x,e[1]+j))
        if n is not None:
            for i in [-1,0,1,2]:
                for y in [min_y-1, min_y]:
                    excepted.add((n[0]+i,y))
        if w is not None:
            for j in [-1,0,1,2]:
                for x in [min_x-1, min_x]:
                    excepted.add((x,w[1]+j))
        if s is not None:
            for i in [-1,0,1,2]:
                for y in [max_y, max_y+1]:
                    excepted.add((s[0]+i,y))
    result = set()
    for vec in pattern:
        for nbr in neighborhood(vec):
            if nbr not in pattern:
                if vec not in excepted:
                    result.add(vec)
                if nbr not in excepted:
                    result.add(nbr)
    return result

def forced_clauses(forced, names):
    "Clauses for forcing a certain subpattern of the preimage"
    for (vec, value) in forced.items():
        if vec not in names:
            print(vec)
            raise Exception
        if value:
            yield [names[vec]]
        else:
            yield [-names[vec]]

def preimages(pattern, forced=None):
    "Enumerate possible preimages"
    clauses, names = gol_preim_inst(pattern)
    if forced is not None:
        clauses += forced_clauses(forced, names)
    with Glucose4(bootstrap_with=clauses) as solver:
        for model in solver.enum_models():
            yield model_to_pattern(model, names)

def preimages_at(pattern, domain, forced=None):
    "Enumerate possible contents of preimage in domain, yielding a full preimage for each"
    clauses, names = gol_preim_inst(pattern)
    if forced is not None:
        clauses += forced_clauses(forced, names)
    with Glucose4(bootstrap_with=clauses) as solver:
        while solver.solve():
            model = solver.get_model()
            yield model_to_pattern(model, names)
            not_current = [-model[names[vec]-1] for vec in domain]
            solver.add_clause(not_current)

def preimage(pattern, forced=None):
    "Return a single preimage, or None if none exist"
    clauses, names = gol_preim_inst(pattern)
    if forced is not None:
        clauses += forced_clauses(forced, names)
    with Glucose4(bootstrap_with=clauses) as solver:
        if solver.solve():
            model = solver.get_model()
            return model_to_pattern(model, names)
        else:
            return None

def model_to_pattern(model, names):
    return {vec : (0 if model[name-1] < 0 else 1) for (vec, name) in names.items()}

def cart_prod(lists):
    "Cartesian product of list of lists"
    if not lists:
        yield []
    else:
        for item in lists[0]:
            for items in cart_prod(lists[1:]):
                yield [item]+items

def verify_spec(name, pattern, size, align, charging, relation, verbose=False, print_patterns=False):
    "Verify the spec of a pattern"
    if verbose:
        print("Verifying that {} satisfies specs".format(name))
    if print_patterns:
        print_pattern(pattern)
    if size is not None:
        min_x = min(x for (x,_) in pattern)
        max_x = max(x for (x,_) in pattern)
        min_y = min(y for (_,y) in pattern)
        max_y = max(y for (_,y) in pattern)
        if size == (max_x-min_x+1, max_y-min_y+1):
            if verbose:
                print("Correct size: {}".format(size))
        else:
            if verbose:
                print("Incorrect size: {} instead of {}".format((max_x-min_x+1, max_y-min_y+1), size))
            return False
    wire_e, wire_n, wire_w, wire_s = wires = find_wires(pattern)
    if verbose:
        print("Wires found at {}".format(wires))
    if align is not None:
        align_e, align_n, align_w, align_s = align
        if align_e is not None:
            real_e = (wire_e[0] - max_x + 1)%3 - 1
            if real_e != align_e:
                if verbose:
                    print("Incorrect east phase alignment: {} instead of {}".format(real_e, align_e))
                return False
        if align_n is not None:
            real_n = (wire_n[1] - min_y - 1)%3 - 1
            if real_n != align_n:
                if verbose:
                    print("Incorrect north phase alignment: {} instead of {}".format(real_n, align_n))
                return False
        if align_w is not None:
            real_w = (wire_w[0] - min_x - 1)%3 - 1
            if real_w != align_w:
                if verbose:
                    print("Incorrect west phase alignment: {} instead of {}".format(real_w, align_w))
                return False
        if align_s is not None:
            real_s = (wire_s[1] - max_y + 1)%3 - 1
            if real_s != align_s:
                if verbose:
                    print("Incorrect south phase alignment: {} instead of {}".format(real_s, align_s))
                return False
        if verbose:
            print("Correct phase alignments: {}".format(align))
    signals = dict()
    if wire_e is not None:
        (x,y) = wire_e
        zero = {(x+i,y+j):int(i==0)
                for i in [0,1]
                for j in [-1,0,1,2]}
        one = {(x+i,y+j):int(i==1)
               for i in [0,1]
               for j in [-1,0,1,2]}
        signals['E'] = [zero, one]
    if wire_n is not None:
        (x,y) = wire_n
        zero = {(x+i,y+j):int(j==0)
                for i in [-1,0,1,2]
                for j in [0,1]}
        one = {(x+i,y+j):int(j==1)
               for i in [-1,0,1,2]
               for j in [0,1]}
        signals['N'] = [zero, one]
    if wire_w is not None:
        (x,y) = wire_w
        zero = {(x+i,y+j):int(i==0)
                for i in [0,1]
                for j in [-1,0,1,2]}
        one = {(x+i,y+j):int(i==1)
               for i in [0,1]
               for j in [-1,0,1,2]}
        signals['W'] = [zero, one]
    if wire_s is not None:
        (x,y) = wire_s
        zero = {(x+i,y+j):int(j==0)
                for i in [-1,0,1,2]
                for j in [0,1]}
        one = {(x+i,y+j):int(j==1)
               for i in [-1,0,1,2]
               for j in [0,1]}
        signals['S'] = [zero, one]
    if verbose and charging:
        print("Checking charging behavior", ", ".join("{} |- {}".format(a,b) for (a,b) in charging))
    for (inp, outp) in charging:
        forced_choices = []
        for d in inp:
            try:        
                forced_choices.append(signals[d])
            except KeyError:
                if verbose:
                    print("Wire {} not found".format(d))
                return False
        for inputs in cart_prod(forced_choices):
            combined_input = dict()
            for input_pat in inputs:
                combined_input.update(input_pat)
            for d in outp:
                try:
                    output_domain = set(signals[d][0])
                except KeyError:
                    if verbose:
                        print("Wire {} not found".format(d))
                    return False
                for preim in preimages_at(pattern, output_domain, forced=combined_input):
                    if not any(all(preim[vec] == signal[vec] for vec in signal)
                               for signal in signals[d]):
                        if verbose:
                            print("Charging {} |- {} failed".format(inp, d))
                        return False
    rel_wires, rel_items = relation
    if verbose:
        
        print("Checking relation", rel_wires, "in {" + ", ".join("".join(str(b) for b in w) for w in rel_items) + "}")
    zero_border = {vec:0 for vec in thick_border(pattern, wires=wires)}
    try:
        wire_choices = cart_prod([list(enumerate(signals[d])) for d in rel_wires])
    except KeyError:
        if verbose:
            print("Some wires not found")
        return False
    seen_items = set()
    for wire_vals in wire_choices:
        combined_wire_pat = dict()
        bit_vals = dict()
        for (d, (bit, wire_pat)) in zip(rel_wires, wire_vals):
            combined_wire_pat.update(wire_pat)
            bit_vals[d] = bit
        preim = preimage(pattern, forced=combined_wire_pat)
        if preim is not None:
            #if verbose:
            #    print_pattern(preim, highlight=zero_border)
            bits = tuple(bit_vals[d] for d in rel_wires)
            seen_items.add(tuple(bit_vals[d] for d in rel_wires))
            combined_wire_pat.update(zero_border)
            zero_preim = preimage(pattern, forced=combined_wire_pat)
            if zero_preim is None:
                if verbose:
                    print("Putting zeros on border failed for {}".format("".join(str(bit) for bit in bits)))
                return False
            else:
                if verbose:
                    print("Found zero-bordered preimage for {}".format("".join(str(bit) for bit in bits)))
                if print_patterns:
                    print_pattern(zero_preim, highlight=zero_border)
    if seen_items == rel_items:
        if verbose:
            print("Success (no other preimages found)")
        return True
    else:
        if verbose:
            print("Pattern implements relation {} in {} instead".format(rel_wires, seen_items))
        return False

def parse_pattern(lines):
    "Parse a pattern from a csv file"
    pattern = dict()
    y = 0
    for line in lines:
        if line[0] == '%':
            continue
        x = 0
        for sym in line:
            if sym in "0123456789":
                pattern[x,y] = int(sym)
                x += 1
        y += 1
    return pattern
                

def print_pattern(pattern, highlight=None):
    if pattern is None:
        print("No pattern")
    else:
        s = ""
        minx = min(p[0] for p in pattern)
        maxx = max(p[0] for p in pattern)
        miny = min(p[1] for p in pattern)
        maxy = max(p[1] for p in pattern)
        for y in range(miny, maxy+1):
            for x in range(minx, maxx+1):
                if (x,y) in pattern:
                    if highlight is None:
                        s += str(pattern[x,y])
                    elif (x,y) in highlight and (x-1,y) not in highlight:
                        s += "[{}".format(pattern[x,y])
                    elif (x,y) not in highlight and (x-1,y) in highlight:
                        s += "]{}".format(pattern[x,y])
                    else:
                        s += " {}".format(pattern[x,y])
                elif highlight is None:
                    s += " "
                else:
                    s += "  "
            s += "]\n" if highlight is not None and (maxx,y) in highlight else "\n"
        print(s)

pattern_list = \
    [
        # Gadgets of section 4
        (os.path.join("gadgets", "charger.cvs"), "charger gadget",
         None, None,
         [('','N')],
         ('N',{(0,),(1,)})),
        (os.path.join("gadgets", "splitter.cvs"), "splitter gadget",
         None, None,
         [('N', 'ENS'), ('S', 'ENS')],
         ('ENS', {(1,0,0),(0,1,1)})),
        (os.path.join("gadgets", "CScombo1.cvs"), "charged turn gadget 1",
         None, None,
         [('', 'ES')],
         ('ES', {(0,1),(1,0)})),
        (os.path.join("gadgets", "CScombo2.cvs"), "charged turn gadget 2",
         None, None,
         [('', 'ES')],
         ('ES', {(0,0),(1,1)})),
        (os.path.join("gadgets", "not.cvs"), "inverter gadget",
         None, None,
         [('E', 'W')],
         ('EW', {(0,1),(1,0)})),
        (os.path.join("gadgets", "crossing.cvs"), "crossing gadget",
         None, None,
         [],
         ('ENWS', {(0,0,1,1),(0,1,1,0),(1,0,0,1),(1,1,0,0)})),
        (os.path.join("gadgets", "and.cvs"), "logic gate gadget",
         None, None,
         [],
         ('ENW', {(1,1,1),(0,1,1),(1,0,0),(0,1,0)})),
        (os.path.join("gadgets", "enforcer.cvs"), "enforcer gadget",
         None, None,
         [('','W')],
         ('W', {(1,)})),
        # 90x90 tile gadgets
        (os.path.join("small_squares", "hor-wire.cvs"), "horizontal wire tile",
         (90,90), (0,None,0,None),
         [],
         ('EW',{(0,0),(1,1)})),
        (os.path.join("small_squares", "ver-wire.cvs"), "vertical wire tile",
         (90,90), (None,0,None,0),
         [],
         ('NS',{(0,0),(1,1)})),
        (os.path.join("small_squares", "ne-turn.cvs"), "NE turn tile",
         (90,90), (1,1,None,None),
         [],
         ('NE',{(0,0),(1,1)})),
        (os.path.join("small_squares", "nw-turn.cvs"), "NW turn tile",
         (90,90), (None,1,1,None),
         [],
         ('NW',{(0,0),(1,1)})),
        (os.path.join("small_squares", "sw-turn.cvs"), "SW turn tile",
         (90,90), (None,None,-1,-1),
         [],
         ('SW',{(0,0),(1,1)})),
        (os.path.join("small_squares", "se-turn.cvs"), "SE turn tile",
         (90,90), (-1,None,None,-1),
         [],
         ('SE',{(0,0),(1,1)})),
        (os.path.join("small_squares", "not.cvs"), "NOT gate tile",
         (90,90), (0,None,1,None),
         [],
         ('EW',{(0,1),(1,0)})),
        (os.path.join("small_squares", "one.cvs"), "always-1 tile",
         (90,90), (None,None,0,None),
         [],
         ('W',{(1,)})),
        (os.path.join("small_squares", "split.cvs"), "splitter tile",
         (90,90), (-1,-1,None,-1),
         [],
         ('ENS',{(0,0,0),(1,1,1)})),
        (os.path.join("small_squares", "cross.cvs"), "crossing tile",
         (90,90), (-1,0,0,-1),
         [],
         ('ENWS',{(0,0,0,0),(0,1,0,1),(1,0,1,0),(1,1,1,1)})),
        (os.path.join("small_squares", "or.cvs"), "OR gate tile",
         (90,90), (0,0,None,-1),
         [],
         ('ENS',{(0,0,0),(1,0,1),(1,1,0),(1,1,1)})),
        # 180x90 connector gadgets
        (os.path.join("connectors", "connector-n1-n1.cvs"), "connector -1 to -1",
         (180,90), (-1,None,-1,None),
         [('','EW')],
         ('EW',{(0,0),(1,1)})),
        (os.path.join("connectors", "connector-0-n1.cvs"), "connector 0 to -1",
         (180,90), (-1,None,0,None),
         [('','EW')],
         ('EW',{(0,0),(1,1)})),
        (os.path.join("connectors", "connector-1-n1.cvs"), "connector 1 to -1",
         (180,90), (-1,None,1,None),
         [('','EW')],
         ('EW',{(0,0),(1,1)})),
        (os.path.join("connectors", "connector-n1-0.cvs"), "connector -1 to 0",
         (180,90), (0,None,-1,None),
         [('','EW')],
         ('EW',{(0,0),(1,1)})),
        (os.path.join("connectors", "connector-0-0.cvs"), "connector 0 to 0",
         (180,90), (0,None,0,None),
         [('','EW')],
         ('EW',{(0,0),(1,1)})),
        (os.path.join("connectors", "connector-1-0.cvs"), "connector 1 to 0",
         (180,90), (0,None,1,None),
         [('','EW')],
         ('EW',{(0,0),(1,1)})),
        (os.path.join("connectors", "connector-n1-1.cvs"), "connector -1 to 1",
         (180,90), (1,None,-1,None),
         [('','EW')],
         ('EW',{(0,0),(1,1)})),
        (os.path.join("connectors", "connector-0-1.cvs"), "connector 0 to 1",
         (180,90), (1,None,0,None),
         [('','EW')],
         ('EW',{(0,0),(1,1)})),
        (os.path.join("connectors", "connector-1-1.cvs"), "connector 1 to 1",
         (180,90), (1,None,1,None),
         [('','EW')],
         ('EW',{(0,0),(1,1)}))
    ]

if __name__ == "__main__":
    arg_parser = argparse.ArgumentParser()
    arg_parser.add_argument("--print_patterns", '-p', action="store_true", required=False, help="print all patterns")
    arg_parser.add_argument("--quiet", '-q', action="store_true", required=False, help="print only final result")
    arg_parser.add_argument("--show_numbers", '-s', action="store_true", required=False, help="display pattern numbers and quit")
    arg_parser.add_argument("--number", '-n', type=int, required=False, help="verify only pattern with given number")
    arg_parser.add_argument("--encoding", '-e', choices=["bisector", "sort_network", "totalizer"], default="totalizer", help="choose SAT encoding")
    args = arg_parser.parse_args()
    
    if args.show_numbers:
        for (i, data) in enumerate(pattern_list):
            print("{0: >2} ".format(i), data[1])
        quit()

    if args.encoding == "bisector":
        if not args.quiet:
            print("Using bisection encoding")
            print()
        ENCODING = bisector
    elif args.encoding == "sort_network":
        if not args.quiet:
            print("Using sorting network encoding")
            print()
        ENCODING = sort_network
    elif args.encoding == "totalizer":
        if not args.quiet:
            print("Using totalizer encoding")
            print()
        ENCODING = totalizer
    
    verbose = not args.quiet
    print_patterns = args.print_patterns
    if args.number is not None:
        pattern_list = [pattern_list[args.number]]
    for (fname, patname, size, align, charging, relation) in pattern_list:
        with open(fname, 'r') as f:
            lines = f.readlines()
        pattern = parse_pattern(lines)
        res = verify_spec(patname, pattern, size, align, charging, relation, verbose=verbose, print_patterns=print_patterns)
        if not res:
            break
        print()
    else:
        if args.number is None:
            print("All patterns verified")
