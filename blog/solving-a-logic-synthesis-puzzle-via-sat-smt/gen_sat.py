from itertools import *
from z3 import *

def output_connections(num_inputs, x, outputs):
    asserts = []
    for output_idx in range(len(outputs)):
        conn_vars = []
        for gate_idx in range(len(x)):
            conn_var = Bool("g_{:d}_{:d}".format(output_idx, gate_idx))
            conn_vars.append(conn_var)
            conn_constraints = []
            for idx, bits in enumerate(product([False, True], repeat=num_inputs)):
                expr = outputs[output_idx](bits) == x[gate_idx][idx]
                conn_constraints.append(expr)
            asserts.append(Implies(conn_var, And(conn_constraints)))
        asserts.append(Or(conn_vars))
    return asserts

def gate_connections(num_inputs, x, f):
    asserts = []
    for gate_idx in range(num_inputs, len(x)):
        print("Encoding gate {}".format(gate_idx))
        conn_vars = []
        for in1_idx, in2_idx in combinations(range(gate_idx), 2):
            conn_var = Bool("c_{:d}_{:d}_{:d}".format(gate_idx, in1_idx, in2_idx))
            conn_vars.append(conn_var)
            for input_idx, input_bits in enumerate(product(range(2), repeat=num_inputs)):
                for gate_input_idx, gate_input_bits in enumerate(product([False, True], repeat=2)):
                    for gate_out in [False, True]:
                        expr = Implies(And(conn_var,
                                           x[in1_idx][input_idx] == gate_input_bits[0],
                                           x[in2_idx][input_idx] == gate_input_bits[1],
                                           x[gate_idx][input_idx] == gate_out),
                                       f[gate_idx - num_inputs][gate_input_idx] == gate_out)
                        asserts.append(expr)
        asserts.append(Or(conn_vars))
    return asserts

def f_constraints(f):
    is_and = lambda gate: And(Not(gate[0]), Not(gate[1]), Not(gate[2]), gate[3])
    is_or = lambda gate: And(Not(gate[0]), gate[1], gate[2], gate[3])
    is_not = lambda gate: And(gate[0], Not(gate[1]) == gate[2], Not(gate[3]))

    asserts = []
    for gate in f:
        gate_filters = [is_and(gate), is_or(gate), is_not(gate)]
        asserts.append(Or(gate_filters))
    if len(f) > 0:
        asserts.append(AtMost([is_not(gate) for gate in f] + [2]))
    return asserts

def encode(num_inputs, outputs, num_inner_gates):
    # Create variables (and values for inputs) for each x_i, given concrete inputs
    x = [[Bool("x{:d}{}".format(gate_idx, val)) for val in product(range(2), repeat=num_inputs)]
         for gate_idx in range(num_inputs + num_inner_gates)]
    # Replace variables for inputs by concrete values
    for input_idx in range(num_inputs):
        for idx, bits in enumerate(product(range(2), repeat=num_inputs)):
            x[input_idx][idx] = BoolVal(bits[input_idx])

    # Create functions f:B^2-->B realised by the inner gates
    f = [[Bool("f{:d}{}".format(gate_idx, val)) for val in product(range(2), repeat=2)]
         for gate_idx in range(num_inputs, len(x))]

    # Add simplified assertions to goal
    goal = Goal()
    for assrt in output_connections(num_inputs, x, outputs) + gate_connections(num_inputs, x, f) + f_constraints(f):
        goal.add(simplify(assrt))

    # Reduce cardinality constraints; transform to CNF
    to_cnf = Then(Tactic("card2bv"), Tactic("tseitin-cnf"))
    subgoals = to_cnf(goal)
    assert len(subgoals) == 1, "Tactic should have resulted in a single goal"
    assert not subgoals[0].inconsistent(), "Found to be UNSAT during pre-processing"
    return subgoals[0].dimacs() + "\n"

def main():
    print("Using {}".format(z3.get_full_version()))
    # Full adder example (impossible with 8 restricted gates; possible with 9)
    sum = lambda inputs: Xor(Xor(inputs[0], inputs[1]), inputs[2])
    carry = lambda inputs: Or(And(inputs[0], inputs[1]), And(Xor(inputs[0], inputs[1]), inputs[2]))
    outputs = [sum, carry]
    # Original puzzle (possible with 22 gates)
    g0 = lambda inputs: Not(inputs[0])
    g1 = lambda inputs: Not(inputs[1])
    g2 = lambda inputs: Not(inputs[2])
    outputs = [g0, g1, g2]
    dimacs = encode(3, outputs, 22)
    with open("dump.cnf", 'w') as writer:
        writer.write(dimacs)

if __name__ == '__main__':
    main()
