# pycosa [![Build Status](https://travis-ci.org/smba/pycosa.svg?branch=main)](https://travis-ci.org/smba/pycosa)
This is a collection of sampling strategies for (binary) configuration spaces. The algorithms implemented here are merely intended for demonstration and teaching purposes. A more mature tool box that has been widely used for configuration sampling is [SPLConqueror](https://github.com/se-sic/SPLConqueror).
## Documentation
### Feature Models

#### Input Formats
##### DIMACS
#### Internal Representation
##### Boolean Expression
##### Bit Vectors

### Sampling Strategies
#### Main Effects Sampling
This strategy is implemented in the class `pycosa.sampling.CoverageSampler`.

##### t-wise Sampling
##### Negative t-wise Sampling

#### Random Sampling
##### Solver-based Random Sampling
This strategy is implemented in the class `pycosa.sampling.NaiveRandomSampler`.

##### Sampling with Diversity Promotion
To mitigate the inehrent bias when entirely relying on a solver to draw samples, mutation of the order of literals in clauses and clauses themselves can increase the variation between obtained samples. This approach implements the SATIBEA/diversity promotion approach (see below), which is an extension to the simple solver-based random sampling. The mutation steps significantly increase the overhead when sampling.

This strategy is implemented in the class `pycosa.sampling.DiversityPromotionSampler`.

Orignal Paper: [_Combining Multi-Objective Search and Constraint Solving for Configuring Large Software Product Lines_](https://doi.org/10.1109/ICSE.2015.69)

##### Distance-based Sampling
This strategy is implemented in the class `pycosa.sampling.DistanceSampler`.

Orignal Paper: [_Distance-Based Sampling of Software Configuration Spaces_](https://doi.org/10.1109/ICSE.2015.69)

##### Sampling with Binary Decision Diagrams (BDD)
This strategy is implemented in the class `pycosa.sampling.BBDSampler`.

Orignal Paper: [_Finding near-optimal configurations in product lines by random sampling_](https://doi.org/10.1145/3106237.3106273)

#### Importance Sampling
This strategy is implemented in the class `pycosa.sampling.ImportanceSampler`.

## Getting Started
### Install
You can install the library includin dependencies directly from this repository using `pip`:
```
pip install git+https://github.com/smba/pycosa.git@main
```
