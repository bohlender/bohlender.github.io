from itertools import product
from z3 import *  # Provided by pip install z3-solver

DIGIT_SEGMENTS = {
    0: 'abcefg',
    1: 'cf',
    2: 'acdeg',
    3: 'acdfg',
    4: 'bcdf',
    5: 'abdfg',
    6: 'abdefg',
    7: 'acf',
    8: 'abcdefg',
    9: 'abcdfg'
}

# Domain (and converters) to represent Digits
DigitSort, digits = EnumSort('Digit', ('0', '1', '2', '3', '4', '5', '6', '7', '8', '9'))
def mk_digit(i: int): return digits[i]
digit2int = {d: int(str(d)) for d in digits}

# Domain (and converters) to index/identify the ten observable patterns
IndexSort, indices = EnumSort('Index', ('0', '1', '2', '3', '4', '5', '6', '7', '8', '9'))
def mk_index(i: int): return indices[i]
index2int = {i: int(str(i)) for i in indices}

# Domain (and converters) to represent segments/wires
SegmentSort, segments = EnumSort('Segment', ('a', 'b', 'c', 'd', 'e', 'f', 'g'))
def mk_segment(char: str): return segments[ord(char) - ord('a')]
segment2char = {s: str(s) for s in segments}


class PuzzleEncoder:
    """Characterises the decoding problem posed in a line of the puzzle input."""

    def logic(self) -> str:
        """The logic that the produced encoding is in."""
        pass

    def encode_core(self) -> list[ExprRef]:
        """Characterise the part common to all decoding problems."""
        pass

    def encode_variant(self, patterns: list[str]) -> list[ExprRef]:
        """Characterise the distinctive part of a decoding problem, i.e. the observed patterns."""
        pass

    def interpret(self, model: ModelRef) -> list[int]:
        """Interpret the model to extract the mapping 'observed pattern index -> represented digit'."""
        pass


def solve_puzzle(filename: str, encoder: PuzzleEncoder):
    s = SolverFor(encoder.logic())
    s.add(encoder.encode_core())

    # Solve problem instance encoded in each line of the input file & sum the decoded output
    acc = 0
    for line in open(filename).read().splitlines():
        observed_patterns, output = parse_line(line)

        s.push()
        s.add(encoder.encode_variant(observed_patterns))
        assert s.check() == sat, 'Cannot find satisfying interpretation'
        idx2dig = encoder.interpret(s.model())
        s.pop()

        # Decode and add output value to accumulator
        output_digits = [idx2dig[observed_patterns.index(pattern)] for pattern in output]
        acc += sum(d * factor for d, factor in zip(output_digits, [1000, 100, 10, 1]))

    return acc


class HighLevelEncoder(PuzzleEncoder):
    """A high-level encoding featuring quantifiers, uninterpreted functions and finite domains"""

    def __init__(self):
        self.digit_segment = Function('digitSegment', DigitSort, SegmentSort, BoolSort())
        self.perm = Function('Perm', SegmentSort, SegmentSort)
        self.perm_digit_segment = Function('PermDigitSegment', DigitSort, SegmentSort, BoolSort())
        self.pattern_segment = Function('patternSegment', IndexSort, SegmentSort, BoolSort())
        self.idx2dig = Function('Idx2dig', IndexSort, DigitSort)

    def logic(self) -> str:
        return 'UF'  # more precisely 'UFFD' but that's not known to Z3

    def encode_core(self) -> list[ExprRef]:
        res = []

        # Characterise digitSegment according to DIGIT_SEGMENTS
        d = Const('d', DigitSort)
        s = Const('s', SegmentSort)
        res.append(
            ForAll([d, s],
                   self.digit_segment(d, s) == Or([
                       And(d == mk_digit(dig), Or([s == mk_segment(char) for char in string]))
                       for dig, string in DIGIT_SEGMENTS.items()])))

        # Perm should be a bijection
        s_prime = Const("s'", SegmentSort)
        res.append(ForAll([s, s_prime],
                          (s == s_prime) == (self.perm(s) == self.perm(s_prime))))

        # Characterise how PermDigitSegment derives from digitSegment and Perm, i.e.
        # PermDigitSegment(d, Perm(s)) == digitSegment(d, s)
        res.append(
            ForAll([d, s],
                   self.perm_digit_segment(d, self.perm(s)) == self.digit_segment(d, s)))

        # Require Idx2dig to be correct wrt. its role as "decoding function", i.e.
        # PermDigitSegment(Idx2dig(i), s) == patternSegment(i, s)
        i = Const('i', IndexSort)
        res.append(ForAll([i, s],
                          self.perm_digit_segment(self.idx2dig(i), s) == self.pattern_segment(i, s)))

        return res

    def encode_variant(self, patterns: list[str]) -> list[ExprRef]:
        res = []

        # Characterise `patternSegment` according to `patterns`
        i = Const('i', IndexSort)
        s = Const('s', SegmentSort)
        res.append(
            ForAll([i, s],
                   self.pattern_segment(i, s) == Or([
                       And(i == mk_index(idx), Or([s == mk_segment(char) for char in string]))
                       for idx, string in enumerate(patterns)])))

        return res

    def interpret(self, model: ModelRef) -> list[int]:
        return [digit2int[model.eval(self.idx2dig(i))] for i in indices]


class MidLevelEncoder(PuzzleEncoder):
    """A quantifier-free mid-level encoding featuring uninterpreted functions and finite domains"""

    def __init__(self):
        self.digit_segment = Function('digitSegment', DigitSort, SegmentSort, BoolSort())
        self.perm = Function('Perm', SegmentSort, SegmentSort)
        self.perm_digit_segment = Function('PermDigitSegment', DigitSort, SegmentSort, BoolSort())
        self.pattern_segment = Function('patternSegment', IndexSort, SegmentSort, BoolSort())
        self.idx2dig = Function('Idx2dig', IndexSort, DigitSort)

    def logic(self) -> str:
        return 'QF_UFDT'  # more precisely 'QF_UFFD' but that's not known to Z3

    def encode_core(self) -> list[ExprRef]:
        res = []

        # Characterise digitSegment according to DIGIT_SEGMENTS
        for d, s in product(digits, segments):
            expected = segment2char[s] in DIGIT_SEGMENTS[digit2int[d]]
            res.append(self.digit_segment(d, s) == expected)

        # Perm should be a bijection
        for s, other in product(segments, segments):
            res.append((s == other) == (self.perm(s) == self.perm(other)))

        # Characterise how PermDigitSegment derives from digitSegment and Perm, i.e.
        # PermDigitSegment(d, Perm(s)) == digitSegment(d, s)
        for d, s in product(digits, segments):
            res.append(self.perm_digit_segment(d, self.perm(s)) == self.digit_segment(d, s))

        # Require Idx2dig to be correct wrt. its role as "decoding function", i.e.
        # PermDigitSegment(Idx2dig(i), s) == patternSegment(i, s)
        for i, s in product(indices, segments):
            res.append(self.perm_digit_segment(self.idx2dig(i), s) == self.pattern_segment(i, s))

        return res

    def encode_variant(self, patterns: list[str]) -> list[ExprRef]:
        res = []

        # Characterise `patternSegment` according to `patterns`
        for i, seg in product(indices, segments):
            expected = segment2char[seg] in patterns[index2int[i]]
            res.append(self.pattern_segment(i, seg) == expected)

        return res

    def interpret(self, model: ModelRef) -> list[int]:
        return [digit2int[model.eval(self.idx2dig(i))] for i in indices]


class LowLevelEncoder(PuzzleEncoder):
    """A quantifier-free low-level encoding featuring finite domains. Effectively a SAT instance."""

    def __init__(self):
        self.digit_segment = {(d, s): Bool(f'digitSegment({d},{s})') for d, s in product(digits, segments)}
        self.perm = {s: Const(f'Perm({s})', SegmentSort) for s in segments}
        self.perm_digit_segment = {(d, s): Bool(f'PermDigitSegment({d},{s})') for d, s in product(digits, segments)}
        self.pattern_segment = {(i, s): Bool(f'patternSegment({i},{s})') for i, s in product(indices, segments)}
        self.idx2dig = {i: Const(f'Idx2dig({i})', DigitSort) for i in indices}

    def logic(self) -> str:
        return 'QF_FD'

    def encode_core(self) -> list[ExprRef]:
        res = []

        # Characterise digitSegment according to DIGIT_SEGMENTS
        for d, s in product(digits, segments):
            expected = segment2char[s] in DIGIT_SEGMENTS[digit2int[d]]
            res.append(self.digit_segment[(d, s)] == expected)

        # Perm should be a bijection
        res.append(Distinct(list(self.perm.values())))

        # Characterise how PermDigitSegment derives from digitSegment and Perm, i.e.
        # PermDigitSegment(d, Perm(s)) == digitSegment(d, s)
        for s, perm_s, d in product(segments, segments, digits):
            res.append(Implies(self.perm[s] == perm_s,
                               self.perm_digit_segment[(d, perm_s)] == self.digit_segment[(d, s)]))

        # Require Idx2dig to be correct wrt. its role as "decoding function", i.e.
        # PermDigitSegment(Idx2dig(i), s) == patternSegment(i, s)
        for i, d, s in product(indices, digits, segments):
            res.append(Implies(self.idx2dig[i] == d,
                               self.perm_digit_segment[(d, s)] == self.pattern_segment[(i, s)]))

        return res

    def encode_variant(self, patterns: list[str]) -> list[ExprRef]:
        res = []

        # Characterise `patternSegment` according to `patterns`
        for i, s in product(indices, segments):
            expected = segment2char[s] in patterns[index2int[i]]
            res.append(self.pattern_segment[(i, s)] == expected)

        return res

    def interpret(self, model: ModelRef) -> list[int]:
        return [digit2int[model.eval(self.idx2dig[i])] for i in indices]


def parse_line(line: str):
    """Map 'adec ... ab | dc ... cdbaf' to (['acde', ..., 'ab'], ['cd' ... 'abcdf'])"""

    def sort_chars(s):
        return ''.join(sorted(s))

    return [[sort_chars(s) for s in part.split()] for part in line.split('|')]


if __name__ == '__main__':
    if len(sys.argv) == 2:
        print(solve_puzzle(sys.argv[1], LowLevelEncoder()))  # Try other encoders
    else:
        print('Expecting one argument: the path to the puzzle input file')
