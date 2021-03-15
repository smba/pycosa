import itertools
import logging
import random
import z3

from pycosa.features import FeatureModel
import numpy as np
import pandas as pd

import abc

class Sampler(metaclass=abc.ABCMeta):
    
    def __init__(self, fm):
        self.fm = fm
        
    @abc.abstractmethod
    def sample(self, **kwargs) -> pd.DataFrame:
        pass

    def sample_to_dataframe(self, input_sample):
        n_options = len(self.fm.feature_dict)

        solutions = [FeatureModel.int_to_config(solution.as_long(), n_options) for solution in input_sample]
        solutions = np.vstack(solutions) == 1
        solutions = pd.DataFrame(solutions, columns=list(self.fm.feature_dict.values()))

        return solutions

class CoverageSampler(Sampler):
    '''
    This class implements sampling strategies with regard to main effects, such as 
    single features' or interactions' influences. This comprises both feature-wise, t-wise
    and negative-featurewise / negative-t-wise sampling.
    
    Brief summary of sampling strategies:
    
    Feature-wise sampling: 
    Activates one feature at a time while minimizing the total 
    number of set of activated features. This usually only activates the mandatory features 
    plus those implied by the one feature selected. The total number of configurations should be
    equal to the number of optional features.
    
    T-wise sampling: 
    Similarly to feature-wise sampling, this activates a combination of T features
    per configuration test for this interaction's influence. Again, the total number of selected features 
    is minimized, such that only implied and mandatory features are selected. The number of configurations cannot
    be greater than 'N over T', where N is the total number of features and T is the target interaction degree. 
    
    Negative feature-wise sampling: 
    Similar to feature-wise sampling with the exception that each optional feature
    is de-selected while the the total number of selected features is maximized. Here, we aim at identifying the 
    influence caused by the absence of individual features.
    
    Negative t-wise sampling: 
    Similar to t-wise sampling, but the combination of T features is de-selected and the total
    number of features is maximized. Here, we aim at identifying the influence caused by the absence 
    of a feature combination.
        
    '''
    
    def __init__(self, fm):
        self.fm = fm
    
    def _find_optional_features(self):
        n_options = len(self.fm.feature_dict)
  
        clauses = self.fm.clauses
        target = self.fm.target
        
        # Identify all non-mandatory (=optional) features
        opts = []
        for opt in range(n_options):

            solver = z3.Solver()
            solver.add(clauses)
            
            # check, if we can set opt to zero
            solver.add( z3.Extract(opt, opt, target) == 0 )
            if solver.check() == z3.sat: opts.append(opt)
            
        return opts
    
    def _find_minimal_configuration(self, solutions, target):
        
        # initialize a new optimizer
        optimizer = z3.Optimize()
            
        # add feature model clauses
        n_options = len(self.fm.feature_dict)
        constraints = self.fm.clauses
        optimizer.add(constraints)
            
        # add previous solutions as constraints
        for solution in solutions:
            optimizer.add(solution != target)
                
        # function not that counts the number of enabled features
        func = z3.Sum([z3.ZeroExt(n_options, z3.Extract(i, i, target)) for i in range(n_options)])
            
        # minimize number of enabled features
        optimizer.minimize(func)
            
        if optimizer.check() == z3.sat:
            solution = optimizer.model()[target]
        else:
            logging.warn("Could not find a minimal solution different from previous configurations.")
            solution = None
            
        return solution
    
    def sample(
            self, 
            t: int, 
            negwise: bool = False,
            include_minimal: bool = False):

        opts = self._find_optional_features()
        
        n_options = len(self.fm.feature_dict)
        constraints = self.fm.clauses
        target = self.fm.target
        
        logging.debug("Discarding {} mandatory options.".format(n_options - len(opts)))
    
        solutions = []
        for interaction in itertools.combinations(opts, t):
            
            # initialize a new optimizer
            optimizer = z3.Optimize()
            
            # add feature model clauses
            optimizer.add(constraints)
            
            # add previous solutions as constraints
            for solution in solutions:
                optimizer.add(solution != target)
            
            for opt in interaction:
                if not negwise:
                    constraint = z3.Extract(opt, opt, target) == 1
                else:
                    constraint = z3.Extract(opt, opt, target) == 0
                    
                optimizer.add(constraint)
            
            # function that counts the number of enabled features
            func = z3.Sum([z3.ZeroExt(n_options, z3.Extract(i, i, target)) for i in range(n_options)])
            
            if not negwise:
                optimizer.minimize(func)
            else:
                optimizer.maximize(func)
            
            if optimizer.check() == z3.sat:
                solution = optimizer.model()[target]
                constraints.append(solution != target)
                solutions.append(solution)
        
        # include a configuration with the minimum number of features enabled
        if include_minimal:
            minimal_config = self._find_minimal_configuration(solutions, target)
            solutions.append(minimal_config)

        solutions = self.sample_to_dataframe(solutions)
    
        return solutions
    
class DistanceSampler(Sampler):
    '''
    This class implements uniform random sampling with distance constraints. 
    The main idea is that for all configurations, a random number of features 
    is selected in order to obtain a representative configuration sample. 
    This aims at avoiding bias introduced by the constraint solver.
    
    Reference: 
    C. Kaltenecker, A. Grebhahn, N. Siegmund, J. Guo and S. Apel, 
    "Distance-Based Sampling of Software Configuration Spaces," 
    2019 IEEE/ACM 41st International Conference on Software Engineering (ICSE), 
    Montreal, QC, Canada, 2019, pp. 1084-1094, doi: 10.1109/ICSE.2019.00112.
    '''
    
    def __init__(self, fm: FeatureModel):
        self.fm = fm
    
    def sample(self, size: int):
        
        n_options = len(self.fm.feature_dict)
        origin = z3.BitVecVal("0" * n_options, n_options)
  
        clauses = self.fm.clauses
        target = self.fm.target
        
        clauses = z3.And(clauses)
        
        # for efficiency purposes, we use one solver instance
        # for each possible distance from the origin
        solvers = {i: z3.Solver() for i in range(1, n_options)}
        for index in solvers.keys(): 
            solvers[index].add(clauses)
            solvers[index].add(DistanceSampler.__hamming(origin, target, 1) == index)
            
        # set of existing solutions
        solutions = []
        
        # unsatisfiable distances
        available_distances = list(range(1, n_options))
        unsatisfiable = False
        sample_sized_reached = False
        
        while not (unsatisfiable or sample_sized_reached):
            distance = np.random.choice(available_distances)

            if solvers[distance].check() == z3.sat:
                solution = solvers[distance].model()[target]
                solvers[distance].add(target != solution)
                solutions.append(solution)
            else:
                available_distances.remove(distance)
    
            unsatisfiable = (len(available_distances) == 0)
            sample_sized_reached = (len(solutions) == size)
                    
        solutions = self.sample_to_dataframe(solutions)

        return solutions
    
    @staticmethod
    def __hamming(v1, v2, target):
        '''
        Auxiliary method that implements the Hamming or Manhattan distance for bit vectors.
        '''
        h = v1 ^ v2
        s = max(target.bit_length(), v1.size().bit_length())
        return z3.Sum([z3.ZeroExt(s, z3.Extract(i, i, h)) for i in range(v1.size())])
    
class NaiveRandomSampler(Sampler):
    '''
    This sampling stategy uses a constraint solver to obtain a configuration sample. As solvers
    re-use paths to solutions (configuration in this context), this results in sample sets that share
    many assignments to variables, i.e., the configurations are quite similar and clustered (little variation).
    
    NOTE: For meaningful uniform random sampling, please use either the DistanceSampler or 
    the DiversityPromotionSampler form this module. This implementation is primarily intended for
    demonstration purposes and a bad example for random sampling in particular!
    '''
    
    def __init__(self, fm: FeatureModel):
        self.fm = fm
        
    def sample(self, sample_size: int):  
        clauses = self.fm.clauses
        target = self.fm.target
        
        solver = z3.Solver()
        
        # add clauses to solver instance
        solver.add(z3.And(clauses))
        
        # container for configurations
        solutions = []
        
        while (solver.check() == z3.sat) and len(solutions) < sample_size:
            solution = solver.model()[target]
            
            # add new clause such that solutions do repeat themselves
            solver.add(target != solution)
            
            # add solution to the solutions
            solutions.append(solution)
            
        solutions = self.sample_to_dataframe(solutions)

        return solutions
    
class DiversityPromotionSampler(Sampler):
    '''
    This sampling technique aims at providing a diverse / more representative configuration sampling strategy
    by mitigating the bias introduced by using a constraint solver (cf. NaiveRandomSampler). For each configuration, 
    the sampling strategy shuffles both the order of the clauses in the feature model CNF as well as the order of
    literals in each clause (SATIBEA approach). While not very efficient, this results in dissimilar solutions
    and an overall more diverse configuration sample.
    
    NOTE: For efficient random sampling, it is preferable to use the DistanceSampler, this implementation
    should primarily serve for demonstration purposes! 
    
    Reference:
    Christopher Henard, Mike Papadakis, Mark Harman, and Yves Le Traon. 
    "Combining multi-objective search and constraint solving for configuring large software product lines". 
    In Proceedings of the 37th International Conference on Software Engineering - Volume 1 (ICSE 2015). 
    IEEE Press, 517–528.
    '''
    def __init__(self, fm: FeatureModel):
        self.fm = fm
        
    def sample(self, sample_size: int):
        solutions = []
        
        satisfiable = True
        while satisfiable and len(solutions) < sample_size:
            
            # shuffle
            self.fm.shuffle()
            
            clauses = self.fm.clauses
            target = self.fm.target
            
            # feed constraints to solver
            solver = z3.Solver()
            solver.add(z3.And(clauses))
            
            # add previous solutions (shuffled) to new solver
            if len(solutions) > 1: 
                solutions = random.sample(solutions, len(solutions))
            
            for solution in solutions:
                solver.add(target != solution)
            
            if solver.check() == z3.sat:
                solution = solver.model()[target]
                solutions.append(solution)
            else:
                satisfiable = False
        
        solutions = self.sample_to_dataframe(solutions)

        return solutions

class BBDSampler(Sampler):
    '''
    This class implements consistent uniform random sampling by partitioning the configuration space. The idea
    is to construct a binary decision diagram (BDD) for an existing feature model. Each distinct path in the BDD
    represents a partition of the confiuration space. For each path, for some, but not all configuration options values
    are assigned, leaving the un-assigned free to select from. By sampling across such partitions, one obtains a true
    random set of valid configurations.

    The construction of a BBD is time-consuming and does not scale well for large and complex feature models, however,
    this approach asserts randomness of the set of sampled configurations.

    References:
    Jeho Oh, Don Batory, Margaret Myers, and Norbert Siegmund. 2017. Finding near-optimal configurations
    in product lines by random sampling. In Proceedings of the 2017 11th Joint Meeting on Foundations of
    Software Engineering (ESEC/FSE 2017). Association for Computing Machinery, New York, NY, USA, 61–71.
    DOI:https://doi.org/10.1145/3106237.3106273
    '''
    
    def sample(self, **kwargs) -> pd.DataFrame:
        '''
        '''
        pass

class ImportanceSampler(Sampler):
    '''
    This is a class that implements configuration sampling with pre-defined probabilities for each configuration 
    option and/or interaction.
    '''
    
    def sample(self, **kwargs) -> pd.DataFrame:
        '''
        '''
        pass 
    
    
    