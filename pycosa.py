from typing import Sequence
import numpy as np
import z3

class FeatureModel:
    
    def __init__(self):
        pass
    
    @staticmethod
    def create(path: str):
        fm = FeatureModel()
        
        clauses, feature_dict = FeatureModel.__parse_dimacs(path)
        fm.clauses = clauses
        fm.features = list(feature_dict.values())
        fm.feature_dict = feature_dict
        print(fm.features)
        return fm
        
    @staticmethod
    def __parse_dimacs(path: str) -> (Sequence[Sequence[int]], dict):
        '''
        :param path:
        :return:
        '''
    
        dimacs = list()
        dimacs.append(list())
        with open(path) as mfile:
            lines = list(mfile)
    
            # parse names of features from DIMACS comments (lines starting with c)
            feature_lines = list(filter(lambda s: s.startswith("c"), lines))
            feature_names = dict(map(lambda l: (int(l.split(" ")[1]), l.split(" ")[2].replace("\n", "")), feature_lines))
    
            # remove comments
    
        dimacs = list()
        dimacs.append(list())
        with open(path) as mfile:
            lines = list(mfile)
    
            # parse names of features from DIMACS comments (lines starting with c)
            feature_lines = list(filter(lambda s: s.startswith("c"), lines))
            feature_names = dict(map(lambda l: (int(l.split(" ")[1]), l.split(" ")[2].replace("\n", "")), feature_lines))
    
            # remove comments
            lines = list(filter(lambda s: not s.startswith("c"), lines))
            n_options = int(lines[0].split(" ")[2])

            for line in lines:
                tokens = line.split()
                if len(tokens) != 0 and tokens[0] not in ("p", "c"):
                    for tok in tokens:
                        lit = int(tok)
                        if lit == 0:
                            dimacs.append(list())
                        else:
                            dimacs[-1].append(lit)
            assert len(dimacs[-1]) == 0
            dimacs.pop()
    
        return dimacs, feature_names

    @staticmethod
    def convert_dimacs_to_bool_model(dimacs: Sequence[Sequence[int]], features: dict) -> (Sequence[z3.Or], dict):
        '''
        :param dimacs:
        :param features:
        :return:
        '''
    
        n_options = len(features)
    
        clauses = []
    
        # create bool literals for each feature
        # index corresponds to the number used in the dimacs clauses
        literals = dict()
        for index in features:
            literals[index] = z3.Bool(features[index])
    
        # add clauses of variability model
        for clause in dimacs:
            c = []
            for opt in clause:
                if opt >= 0:                    # Feature opt is selected
                    c.append(literals[opt])
                else:                           # Feature opt is not selected
                    negated = z3.Not(literals[abs(opt)])
                    c.append(negated)
    
            clauses.append(z3.Or(c))
    
        return clauses, literals

    @staticmethod
    def convert_dimacs_to_bit_model(dimacs: Sequence[Sequence[int]], n_options: int) -> (Sequence[z3.Or], z3.BitVec):
        
        clauses = []
        target = z3.BitVec('target', n_options)

        # add clauses of variability model
        for clause in dimacs:
            c = []
            for opt in clause:
                opt_sign = 1 if opt >= 0 else 0
                optid = n_options - abs(opt)
                c.append(z3.Extract(optid, optid, target) == opt_sign)
    
            clauses.append(z3.Or(c))
    
        return clauses, target#


class BooleanFeatureModel(FeatureModel):
    def __init__(self):
        pass
    
class BitFeatureModel(FeatureModel):
    def __init__(self):
        pass

class Sampler:
    def __init__(self, fm: FeatureModel):
        self.fm = fm
    
class TWiseSampler(Sampler):
    
    def __init__(self, fm):
        Sampler.__init__(self, fm)
        
    def sample(self, fm):
        pass # TODO implement here
    
class DistanceSampler(Sampler):
    
    def __init__(self, fm):
        Sampler.__init__(self, fm)

    def sample(self, size: int):# -> np.ndarray:
        n_options = len(self.fm.features)
        origin = z3.BitVecVal("0" * n_options, n_options)
    
        clauses, target = FeatureModel.convert_dimacs_to_bit_model(Distanceself.fm.clauses, n_options)
        clauses = z3.And(clauses)
    
        solver = z3.Solver()
    
        # add esxisting constraints to solver
        solver.add(clauses)
    
        # set of existing solutions
        solutions = []
        for i in range(size):

            while True:
                # sample a random distance
                distance = np.random.randint(0, n_options)
                solver.add(hamming(origin, target, 1) == distance)
    
                if solver.check() == z3.unsat:
                    # remove distance based constraint
                    constraints = solver.assertions()
                    solver.reset()
                    solver.add(constraints[:-1])
    
                else: # solver.check() == z3.sat
                    solution = solver.model()[target]
    
                    # add current solution to solver assertions = new constraint
                    solver.add( target != solution )
    
                    # add current solution to set of solutions
                    solutions.append(solution)
    
                    break
    
        solutions = [int_to_config(solution.as_long(), n_options) for solution in solutions]
        return np.vstack(solutions)#.vstack()
    
def config_to_int(config: np.ndarray) -> int:
    '''
    :param config:
    :return:
    '''
    pass

def int_to_config(i: int, n_options: int) -> np.ndarray:
    '''
    :param i:
    :param n_options:
    :return:
    '''

    offset = n_options - int(np.ceil(np.log2(i)))
    binary_string = "0" * offset + str(bin(i))[2:]
    assert(len(binary_string) == n_options)

    binary = np.array([int(bit) for bit in binary_string])
    return binary

def hamming(V1, V2, target):
    h = V1 ^ V2
    s = max(target.bit_length(), V1.size().bit_length())
    return z3.Sum([z3.ZeroExt(s, z3.Extract(i, i, h)) for i in range(V1.size())])

a = FeatureModel.create("/home/stefan/Desktop/SWTP/model.dimacs")

sam = DistanceSampler(a)
a = sam.sample(20)

print(a)
