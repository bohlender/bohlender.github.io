from itertools import *
from z3 import *

def output_connections(num_inputs, x, outputs):
    asserts = []
    for output_idx in range(len(outputs)):
        conn_vars = []
        for gate_idx in range(len(x)):
            conn_var = Bool("g_{:d}_{:d}".format(output_idx, gate_idx))
            conn_vars.append(conn_var)
            asserts.append(Implies(conn_var, outputs[output_idx](x[:num_inputs]) == x[gate_idx]))
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
            asserts.append(Implies(conn_var, x[gate_idx] == f[gate_idx - num_inputs](x[in1_idx], x[in2_idx])))
        asserts.append(Or(conn_vars))
    return asserts

def f_constraints(f):
    asserts = []
    is_and = lambda gate: And(Not(gate(False, False)), Not(gate(False, True)), Not(gate(True, False)), gate(True, True))
    is_or = lambda gate: And(Not(gate(False, False)), gate(False, True), gate(True, False), gate(True, True))
    is_not = lambda gate: And(gate(False, False), gate(False, True) != gate(True, False), Not(gate(True, True)))

    for gate in f:
        gate_filters = [is_and(gate), is_or(gate), is_not(gate)]
        asserts.append(Or(gate_filters))
    if len(f) > 0:
        asserts.append(AtMost([is_not(gate) for gate in f] + [2]))
    return asserts

def encode(num_inputs, outputs, num_inner_gates):
    # Create variables (and values for inputs) for each x_i
    x = [Bool("x{:d}".format(gate_idx)) for gate_idx in range(num_inputs + num_inner_gates)]

    # Create functions f:B^2-->B realised by the inner gates
    f_sig = [BoolSort()]*3
    f = [Function("f{:d}".format(gate_idx), f_sig) for gate_idx in range(num_inputs, len(x))]

    # Add simplified assertions to solver
    s = Solver()
    constraints = output_connections(num_inputs, x, outputs) + gate_connections(num_inputs, x, f) + f_constraints(f)
    simplified = And([simplify(assrt) for assrt in constraints])
    quantified = ForAll(x[:num_inputs], Exists(x[num_inputs:], simplified) if num_inner_gates > 0 else simplified)
    s.add(quantified)
    return s.to_smt2() + "(get-model)\n"

def main():
    print("Using {}".format(z3.get_full_version()))
    # Full adder example (impossible with 8 restricted gates; possible with 9)
    sum = lambda inputs: Xor(Xor(inputs[0], inputs[1]), inputs[2])
    carry = lambda inputs: Or(And(inputs[0], inputs[1]), And(Xor(inputs[0], inputs[1]), inputs[2]))
    outputs = [sum, carry]
    # Original puzzle (possible with 19 gates)
    g0 = lambda inputs: Not(inputs[0])
    g1 = lambda inputs: Not(inputs[1])
    g2 = lambda inputs: Not(inputs[2])
    outputs = [g0, g1, g2]
    smtlib = encode(3, outputs, 19)
    with open("dump.smt2", 'w') as writer:
        writer.write(smtlib)

if __name__ == "__main__":
    main()
