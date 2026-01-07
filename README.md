This repository holds the implementation of the zequal tool discussed in the CAV 2025 publication. It verifies whether circom 2.1.8 circuits meet the formal definition of consistency which informally states that the constraints encode the same computation as the witness generator.

# Dependencies
Build dependencies:
* Rust (v1.9.0)

Execution dependencies:
* python3 (v3.8.9)
* z3 (v4.15.3)

# Build
The project can either be built natively or via docker. For reproducibility, docker is encouraged.

## Native
```commandline
cargo build
```

## Docker
```commandline
docker build -t zequal:v0 .
```

# Usage 
`zequal` can be executed either via the compiled executable or the python script. The python script includes some 
additional functionality to make it easier to run zequal in bulk and format the outputs and is what we will focus on here.



## Native
```commandline
zequal.py [-h] [-o OUTPUT] [-t TIMEOUT] [-nsa] [-ic] [-osa] [-csv] filenames [filenames ...]

positional arguments:
  filenames             One or more circom files to verify

optional arguments:
  -h, --help            show this help message and exit
  -o OUTPUT, --output OUTPUT
                        Output verifier output in the given directory
  -t TIMEOUT, --timeout TIMEOUT
                        Verifier timeout in seconds
  -nsa, --no-static-analysis
                        Perform verification without static analysis
  -ic, --infer-contract
                        (Unstable) Attempt to infer method contracts for invoked circuits
  -osa, --only-static-analysis
                        Perform verification only with static analysis
  -csv, --output-csv    Output results as a CSV


```

## Docker
```commandline
docker run -v <DIRECTORY_TO_ANALYZE>:/zequal/to_analyze -it zequal:v0
```

With the above command, all `main*.circom` files included in `DIRECTORY_TO_ANALYZE` will be analyzed by zequal. If this 
does not suit the project undergoing analysis, the following command can be used instead:
```commandline
docker run -v <DIRECTORY_TO_ANALYZE>:/zequal/to_analyze -it zequal:v0 \
  python3 ./zequal.py [-h] [-o OUTPUT] [-t TIMEOUT] [-nsa] [-ic] [-osa] [-csv] filenames [filenames ...]

positional arguments:
  filenames             One or more circom files to verify

optional arguments:
  -h, --help            show this help message and exit
  -o OUTPUT, --output OUTPUT
                        Output verifier output in the given directory
  -t TIMEOUT, --timeout TIMEOUT
                        Verifier timeout in seconds
  -nsa, --no-static-analysis
                        Perform verification without static analysis
  -ic, --infer-contract
                        (Unstable) Attempt to infer method contracts for invoked circuits
  -osa, --only-static-analysis
                        Perform verification only with static analysis
  -csv, --output-csv    Output results as a CSV
```
Again, `DIRECTORY_TO_ANALYZE` should specify the directory with the project undergoing analysis.

### Example
As an example, the included circomlib benchmarks can be run via docker with the following command from this directory:
```commandline
docker run -v $(pwd)/examples/circomlib:/zequal/to_analyze -it zequal:v0
```
Note that there are 108 benchmarks, so it can take a while for all the benchmarks to run.