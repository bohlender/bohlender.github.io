from collections import namedtuple
from itertools import *
from random import randint
from timeit import default_timer
from z3 import *

# Configures the complexity of the secret
NUM_POSITIONS = 16
NUM_SYMBOLS = 6

Feedback = namedtuple('Feedback', ['full_matches', 'symbol_matches'])


def eval_guess(secret, guess):
    # Count full matches (position & symbol)
    guess_rest = [a for (a, b) in zip(guess, secret) if a != b]
    secret_rest = [b for (a, b) in zip(guess, secret) if a != b]
    full_match_count = len(guess) - len(guess_rest)

    # Count partial matches (symbol only)
    symbol_match_count = 0
    for symbol in guess_rest:
        try:
            secret_rest.remove(symbol)
            symbol_match_count += 1
        except ValueError:
            pass
    return Feedback(full_match_count, symbol_match_count)


def is_consistent(secret, guess, feedback):
    return feedback == eval_guess(secret, guess)


def is_consistent_with_history(secret, guesses, feedbacks):
    for guess, feedback in zip(guesses, feedbacks):
        if not is_consistent(secret, guess, feedback):
            return False
    return True


def all_secrets():
    return product(range(NUM_SYMBOLS), repeat=NUM_POSITIONS)


def all_feedbacks():
    for full_matches in range(NUM_POSITIONS + 1):
        for symbol_matches in range(NUM_POSITIONS + 1 - full_matches):
            if full_matches == NUM_POSITIONS - 1 and symbol_matches == 1:
                continue
            yield Feedback(full_matches, symbol_matches)


class Game:
    def __init__(self, secret, player):
        self.secret = secret
        self.player = player

    def run(self):
        guess = self.player.initial_guess()
        num_guesses = 1

        # Guess-Feedback loop until exact match is guessed
        while True:
            feedback = eval_guess(self.secret, guess)
            print("{} --> {}".format(guess, feedback))
            if feedback.full_matches == NUM_POSITIONS:
                break
            guess = self.player.make_guess(feedback)
            num_guesses += 1
        return guess, num_guesses


class Player:
    def initial_guess(self):
        raise NotImplementedError()

    def make_guess(self, feedback):
        raise NotImplementedError()


class ExplicitConsistentAi(Player):
    def __init__(self):
        self.last_guess = None
        self.candidates = list(all_secrets())

    def initial_guess(self):
        self.last_guess = self.candidates[0]
        return self.last_guess

    def make_guess(self, feedback):
        self.candidates = [c for c in self.candidates
                           if is_consistent(c, self.last_guess, feedback)
                           and c != self.last_guess]
        return self.initial_guess()


class ExplicitMinimaxAi(Player):
    def __init__(self):
        self.candidates = list(all_secrets())
        self.not_candidates = list()
        self.guesses = list()

    def initial_guess(self):
        # Pick the (not necessarily consistent) candidate with the best worst feedback
        # w.r.t. the size of the set of consistent candidates (smaller = better)
        not_tried_secrets = (c for c in chain(self.candidates, self.not_candidates)
                             if c not in self.guesses)

        best_c = None
        best_size = math.inf
        for c in not_tried_secrets:
            # Partition consistent candidates by feedback
            feedback_occs = {f: 0 for f in all_feedbacks()}
            for s in self.candidates:
                f = eval_guess(s, c)
                feedback_occs[f] += 1

            # Find worst feedback for this c
            max_size = max(feedback_occs.values())

            # Identify the c that has the best worst feedback
            if max_size < best_size:
                best_size = max_size
                best_c = c

        self.guesses.append(best_c)
        return self.guesses[-1]

    def make_guess(self, feedback):
        self.not_candidates.extend(c for c in self.candidates if not is_consistent(c, self.guesses[-1], feedback))
        self.candidates = [c for c in self.candidates if is_consistent(c, self.guesses[-1], feedback)]
        return self.initial_guess()


class LazyExplicitConsistentAi(Player):
    def __init__(self):
        self.guesses = list()
        self.feedbacks = list()
        self.candidates = (c for c in all_secrets()
                           if is_consistent_with_history(c, self.guesses, self.feedbacks))

    def initial_guess(self):
        self.guesses.append(next(self.candidates))
        return self.guesses[-1]

    def make_guess(self, feedback):
        self.feedbacks.append(feedback)
        return self.initial_guess()


class SymbolicConsistentAi(Player):
    def __init__(self):
        self.last_guess = None
        self.solver = SolverFor("QF_FD")  # Solver for quantifier-free constraints over finite domains

        # Possible values at secret positions, i.e. s_0_2 denotes position 0 of secret having symbol 2
        self.secret_vars = [[Bool("s_{}_{}".format(pos, sym)) for sym in range(NUM_SYMBOLS)]
                            for pos in range(NUM_POSITIONS)]

        # Exactly one symbol on each position
        for pos in range(NUM_POSITIONS):
            coeffs = [(sym, 1) for sym in self.secret_vars[pos]]
            self.solver.add(PbEq(coeffs, 1))

    def initial_guess(self):
        status = self.solver.check()

        # Extract guess from solution to constraints
        m = self.solver.model()
        guess = list()
        for pos in range(NUM_POSITIONS):
            for sym in range(NUM_SYMBOLS):
                if is_true(m.eval(self.secret_vars[pos][sym])):
                    guess.append(sym)
                    continue
        assert (len(guess) == NUM_POSITIONS)

        self.last_guess = tuple(guess)
        return self.last_guess

    def make_guess(self, feedback):
        # Fresh "full match" variables for each position
        fm = [FreshBool("fm_{}".format(pos)) for pos in range(NUM_POSITIONS)]

        # Full matches must be consistent with feedback
        fm_coeffs = [(fm_pos, 1) for fm_pos in fm]
        self.solver.add(PbEq(fm_coeffs, feedback.full_matches))

        # Possible full matches
        for pos in range(NUM_POSITIONS):
            self.solver.add(self.secret_vars[pos][self.last_guess[pos]] == fm[pos])

        # Fresh "symbol match" variables for each pair of positions
        sm = [[FreshBool("sm_{}_{}".format(src_pos, dst_pos)) for dst_pos in range(NUM_POSITIONS)]
              for src_pos in range(NUM_POSITIONS)]

        # Symbol matches must be consistent with feedback
        sm_coeffs = [(sm[src_pos][dst_pos], 1) for (src_pos, dst_pos) in
                     permutations(range(NUM_POSITIONS), 2)]
        self.solver.add(PbEq(sm_coeffs, feedback.symbol_matches))

        # Possible symbol matches
        for src_pos in range(NUM_POSITIONS):
            match_exprs = list()
            for dst_pos in range(NUM_POSITIONS):
                if src_pos == dst_pos:
                    continue

                lhs = list()
                lhs.append(Not(fm[src_pos]))
                lhs.append(self.secret_vars[dst_pos][self.last_guess[src_pos]])
                lhs.append(Not(fm[dst_pos]))
                # No previous position in the guess has a symbol match with the current dst_pos
                lhs.extend([Not(sm[prev_pos][dst_pos]) for prev_pos in range(src_pos) if dst_pos != prev_pos])
                # src_pos has no symbol match with a previous dst_pos
                lhs.extend([Not(sm[src_pos][prev_pos]) for prev_pos in range(dst_pos) if src_pos != prev_pos])

                rhs = sm[src_pos][dst_pos]
                match_exprs.append(And(lhs) == rhs)
            self.solver.add(And(match_exprs))

        return self.initial_guess()


def main(player):
    secret = tuple(randint(0, NUM_SYMBOLS - 1) for _ in range(NUM_POSITIONS))
    game = Game(secret, player)

    print("Using {}\n{} <-- Secret".format(game.player.__class__.__name__, secret))
    start_time = default_timer()
    guess, num_guesses = game.run()
    print("Took {} guesses ({:.3}s)".format(num_guesses, default_timer() - start_time))


if __name__ == "__main__":
    # main(ExplicitConsistentAi())
    # main(ExplicitMinimaxAi())
    # main(LazyExplicitConsistentAi())
    main(SymbolicConsistentAi())
