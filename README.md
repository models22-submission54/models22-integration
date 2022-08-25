This is a repository for showcase our formal methodology of proving correctness for SQL implementations of OCL constraints
The repository is based on this reference methodology:

* [Proving correctness for SQL implementations of OCL constraints]().

## Case materials

The repository is structured as follows:

* `config`: place to store configurations.
  * `Example#i.json`: configuration of Example *i* described in the manuscript.
  * `Example#all.json`: all-in-one examples configuration.
* `libs`: place to store jars and reference libraries.
  * `datamodel-*.jar`: refers to the [`datamodel`](https://github.com/oclsqlprover/dm2schema) Java package.
  * `jocl-*.jar`: refers to the [`JavaOCL`](https://github.com/oclsqlprover/JavaOCL) Java package.
* `output`: place to store auto-generated files.
* `scripts`: includes executable scripts.
  * `install-jar.sh` installs locally the required jars in `\libs`.
  * `run.py` simple prototype to generates the theory for proving the correctness.
  * `logger.py` simple logging system for future statistical extension.
* `tools`: stores the essential mappings.
  * `OCL2MSFOL` Mapping from OCL expressions to Many-sorted First-order Logic.
  * `SQL2MSFOL` Mapping from SQL statements to Many-sorted First-order Logic.

## Prerequisites

- (required) `Maven 3` and `Java 1.8` (or higher).

The prototype requires to pull the two reference tools as submodules.
The easiest way to do so is to execute the following `Git` command:
```
git clone https://github.com/oclsqlprover/OCLSQLProver.git
cd OCLSQLProver
git submodule update --init --recursive
```

The reference tools in directory `\tools` (i.e., [OCL2MSFOL](https://github.com/oclsqlprover/OCL2MSFOL) and [SQL2MSFOL](https://github.com/oclsqlprover/SQL2MSFOL)) use two JAR files that parse the datamodel and OCL expression to Java representation. 
These JAR files can be downloaded [here](https://github.com/oclsqlprover/dm2schema/releases/tag/v1.0) and [here](https://github.com/oclsqlprover/JavaOCL/releases/tag/v1.0), and be put into `\libs` directory.
You must install these dependencies into your local Maven repository before you build the reference solution.
Assuming that Maven is in your `PATH` and that the JARs are already downloaded, you can run our script:
```
cd scripts
./install-jars.sh
```

## Using the framework

One might fine tune the script for the following purposes:
* `run.py -b` -- builds the projects
* `run.py -r` -- run the benchmark without building

The `scripts` directory contains the `run.py` script.
At a first time, invoke the tool with the following arguments:
```
python run.py -br -c <config_filename> -s <solver_name>
```
where `<config_filename>` is the configuration filename in the `\config` directory (without file extension)
and `<solver_name>` is the solver of choice (i.e., either `cvc4` or `z3`).

The `config` directory contains the configuration for the scripts:
* `Example#all.json` -- sample configuration with examples that are identical to the examples in the manuscript [Proving correctness for SQL implementations of OCL constraints](). The following show a sample single testcase:
```
        {
            "context": [
                {
                    "name": "self",
                    "type": "Student"
                },
                {
                    "name": "user",
                    "type": "String"
                }
            ],
            "invariants": [
                "Student.allInstances()->forAll(s|not s.age.oclIsUndefined())",
                "not user.oclIsUndefined()"
            ],
            "OCL": "self.name = user", 
            "SQL": "SELECT (SELECT name FROM Student WHERE Student_id = self) = user"
        },
```

### Solver installation
#### On Ubuntu/Linux:
##### Ubuntu:
```
sudo apt-get update
sudo apt-get install cvc4 z3
```
##### Fedora (using dnf):
```
sudo dnf makecache --refresh
sudo dnf -y install cvc4 z3
```
#### On Windows machine:
- z3: Download the archive folder [here](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.17), unzip it and put it in the `PATH` environment.
- cvc4: Download it [here](https://cvc4.cs.stanford.edu/downloads/builds/win64-opt/), unzip it and put it in the `PATH` environment.
**Note**: Depends on the provided commands of these solvers, you may have to change the predefined commands for running the solver in `run.py`, i.e., [here](https://github.com/oclsqlprover/OCLSQLProver/blob/main/scripts/run.py#L155) and [here](https://github.com/oclsqlprover/OCLSQLProver/blob/main/scripts/run.py#L176).

### Running the tool

The script runs the benchmark for the given number of testcases.

For each testcase, the tool generates a MSFOL theory written in SMT2 file. 
The header for the SMT2 file is stored in the `output/header.smt2` file.

Below snippet show the expected output example when running `OCLSQLProver` with configuration `Example#all`:
```
INFO: [prover] Starting at 15:59:54

================================ Testcase 00 ==================================
SubgoalC1: ✓ SubgoalC2: ✓ SubgoalC3: ✓ > Done.                                     

================================ Testcase 01 ==================================
SubgoalC1: ✓ SubgoalC2: ✓ SubgoalC3: ✓ > Done.                                     

================================ Testcase 02 ==================================
SubgoalC1: ✓ SubgoalC2: ✓ SubgoalC3: ✓ > Done.                                     

================================ Testcase 03 ==================================
SubgoalC1: ✓ SubgoalC2: ✓ SubgoalC3: ✓ > Done.                                     

================================ Testcase 04 ==================================
SubgoalC1: ✓ SubgoalC2: ✓ SubgoalC3: ✓ > Done.                                     

================================ Testcase 05 ==================================
SubgoalC1: ✓ SubgoalC2: ✓ SubgoalC3: ✓ > Done.                                     

================================ Testcase 06 ==================================
SubgoalC1: ✓ SubgoalC2: ✓ SubgoalC3: ✓ > Done.                                     

=================================== End ======================================
```

More examples and scenarios are coming in the near future, so stay tuned!
