import itertools
import logging
import random
import warnings

import z3

from pycosa.features import FeatureModel
import numpy as np
import pandas as pd


class Sampler:
    
    def __init__(self, fm):
        self.fm = fm

class CoverageSampler:
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
    
    def sample(
            self, 
            t: int, 
            negwise: bool = False,
            include_minimal: bool = False):
        '''
        
        '''
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
            
        logging.debug("Discarding {} mandatory options.".format(n_options - len(opts)))
    
        constraints = [clause for clause in clauses]
    
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
                opt = opt#.item()
                
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
        
        print(len(solutions), n_options)
        
        # include a configuration with the minimum number of features enabled
        if include_minimal:
            
            # initialize a new optimizer
            optimizer = z3.Optimize()
            
            # add feature model clauses
            optimizer.add(constraints)
            
            # add previous solutions as constraints
            for solution in solutions:
                optimizer.add(solution != target)
                
            # function notthat counts the number of enabled features
            func = z3.Sum([z3.ZeroExt(n_options, z3.Extract(i, i, target)) for i in range(n_options)])
            
            # minimize number of enabled features
            optimizer.minimize(func)
            
            if optimizer.check() == z3.sat:
                solution = optimizer.model()[target]
                solutions.append(solution)
            else:
                logging.warn("Could not find a minimal solution different from previous configurations.")

        solutions = [FeatureModel.int_to_config(solution.as_long(), n_options) for solution in solutions]
        solutions = np.vstack(solutions) == 1
        solutions = pd.DataFrame(solutions, columns = list(self.fm.feature_dict.values()))
    
        return solutions
    
class DistanceSampler:
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
                    
        solutions = [FeatureModel.int_to_config(solution.as_long(), n_options) for solution in solutions]
        solutions = np.vstack(solutions) == 1
        solutions = pd.DataFrame(solutions, columns = list(self.fm.feature_dict.values()))

        return solutions
    
    @staticmethod
    def __hamming(V1, V2, target):
        '''
        Auxiliary method that implements the Hamming or Manhattan distance for bit vectors.
        '''
        h = V1 ^ V2
        s = max(target.bit_length(), V1.size().bit_length())
        return z3.Sum([z3.ZeroExt(s, z3.Extract(i, i, h)) for i in range(V1.size())])
    
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
        n_options = len(self.fm.feature_dict)
  
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
            
        solutions = [FeatureModel.int_to_config(solution.as_long(), n_options) for solution in solutions]
        solutions = np.vstack(solutions) == 1
        solutions = pd.DataFrame(solutions, columns = list(self.fm.feature_dict.values()))

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
        n_options = len(self.fm.feature_dict)
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
        
        solutions = [FeatureModel.int_to_config(solution.as_long(), n_options) for solution in solutions]
        solutions = np.vstack(solutions) == 1
        solutions = pd.DataFrame(solutions, columns = list(self.fm.feature_dict.values()))

        return solutions