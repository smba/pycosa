# pycosa [![Build Status](https://travis-ci.org/smba/pycosa.svg?branch=main)](https://travis-ci.org/smba/pycosa)
This is a collection of sampling strategies for (binary) configuration spaces. The algorithms implemented here are merely intended for demonstration and teaching purposes. A more mature tool box that has been widely used for configuration sampling is [SPLConqueror](https://github.com/se-sic/SPLConqueror).

## Getting Started
### Install
You can install the library including dependencies directly from this repository or upgrade an existing installation using `pip`:
```bash
pip install git+https://github.com/smba/pycosa.git@main # release
pip install --upgrade git+https://github.com/smba/pycosa.git@main # upgrade existing version
```

## Documentation
### Feature Models

#### Input Formats
##### DIMACS
#### Internal Representation
##### Boolean Expression
##### Bit Vectors

### Sampling Strategies
#### 1) Main Effects / Coverage Sampling
This class of strategies is implemented in the class `pycosa.sampling.CoverageSampler`.

##### 1a) t-wise Sampling
The main idea behind this class of strategies it to unveil the individual effect ('main effect') of single features (t-wise; `t = 1`) or higher-order (t-wise; `t > 1`) interactions. The upper bound for the number of configurations returned by a strategy is the binomial coefficient ('n over t') as we generate a sample configuration for each possible interaction of degree t. For each of those, the relevant features are enabled while all (or at least as few as possible) are disabled to extract the effect of the enabled features. The sampling strategy is exhaustively generating all configurations, but does not scale well to higher order interactions.

##### 1b) Negative t-wise Sampling
In opposition to t-wise sampling, the desired features / interactions are *disabled* while the maximum number of features in a configuration is enabled. This similar to t-wise sampling does not scale well to higher-order interactions. This mode can be selected via the attribute `neg = True`.

#### 2) Random Sampling
##### 2a) Solver-based/Naive 'Random' Sampling
This strategy queries configurations as solutions to the feature model. In essence, this represents a depth-first search in the solution space and, as such, the set of connfigurations is likely clustered around a partial solution path and not thus very diverse. This strategy should be mainly used for demonstration purposes, Diversity Promotion, Distance-based Sampling and BDD Sampling aim at mitigiating this pitfall and provide better, or in the latter case even true random sampling. 

The strategy is implemented in the class `pycosa.sampling.NaiveRandomSampler`.

##### 2b) Sampling with Diversity Promotion
To mitigate the inehrent bias when entirely relying on a solver to draw samples, mutation of the order of literals in clauses and clauses themselves can increase the variation between obtained samples. This approach implements the SATIBEA/diversity promotion approach (see below), which is an extension to the simple solver-based random sampling. The mutation steps significantly increase the overhead when sampling.

This strategy is implemented in the class `pycosa.sampling.DiversityPromotionSampler`.

Orignal Paper: [_Combining Multi-Objective Search and Constraint Solving for Configuring Large Software Product Lines_](https://doi.org/10.1109/ICSE.2015.69)

##### 2c) Distance-based Sampling
This strategy is implemented in the class `pycosa.sampling.DistanceSampler`.

Orignal Paper: [_Distance-Based Sampling of Software Configuration Spaces_](https://doi.org/10.1109/ICSE.2015.69)

##### 2d) Sampling with Binary Decision Diagrams (BDD)
This strategy is implemented in the class `pycosa.sampling.BBDSampler`.

Orignal Paper: [_Finding near-optimal configurations in product lines by random sampling_](https://doi.org/10.1145/3106237.3106273)

#### 3 'Quality of Sampling'
##### 3a) Feature Balance
Related paper using feature balance heuristic: [Cost-Efficient Sampling for Performance Prediction of Configurable Systems](https://dl.acm.org/doi/10.1109/ASE.2015.45)

##### 3b) Variance Inflation Factor

#### 4 Importance Sampling
This strategy is implemented in the class `pycosa.sampling.ImportanceSampler`.

