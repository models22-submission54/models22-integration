# models22-integration

This is a repository for showcase our formal methodology of proving correctness for SQL implementations of OCL constraints
The repository is based on this reference methodology:

* [Proving correctness for SQL implementations of OCL constraints]().

## Case materials

The repository is structured as follows:

* `config`: place to store configurations.
  * `examples.json`: a sample configuration.
* `libs`: place to store jars and reference libraries.
  * `datamodel-*.jar`: refers to the [`datamodel`](https://github.com/MoDELSVGU/datamodel) Java package.
  * `jocl-*.jar`: refers to the [`JavaOCL`](https://github.com/MoDELSVGU/JavaOCL) Java package.
* `output`: place to store auto-generated files.
* `scripts`: includes executable scripts.
  * `install-jar.sh` installs locally the required jars in `libs`.
  * `run.py` simple prototype to generates the theory for proving the correctness.
* `tools`: stores the essential mappings.
  * `OCL2MSFOL` Mapping from OCL expressions to Many-sorted First-order Logic.
  * `SQL2MSFOL` Mapping from SQL statements to Many-sorted First-order Logic.

## Prerequisites

- (required) `Maven 3` and `Java 1.8` (or higher).

The prototype requires to pull the two reference tools as submodules.
The easiest way to do so is to execute the following `Git` command:
```
git clone https://github.com/npbhoang/models22-integration.git
git submodule update --init --recursive
```

The reference tools in `tools` uses two JAR files that provide the datamodel and OCL expression Java representation. 
These JAR files are located in `lib` directory.
You must install these dependencies into your local Maven repository before you build the reference solution.
Assuming that Maven is in your `PATH`, you can run this Bash script:

```
cd scripts
./install-jars.sh
```

## Using the framework

The `scripts` directory contains the `run.py` script.
At a first glance, invoke it the following arguments:
```
python run.py -br -c <configname>
```
One might fine tune the script for the following purposes:
* `run.py -b` -- builds the projects
* `run.py -r` -- run the benchmark without building
* `run.py -v` -- visualizes the results of the latest benchmark (not yet implemented!)
* `run.py -t` -- build the project and run tests (usually unit tests as defined for the given solution)
* `run.py -d` -- runs the process in debug mode, i.e. with the `Debug` environment variable set to `true`

The `config` directory contains the configuration for the scripts:
* `examples.json` -- sample configuration with examples that are identical to the examples in the manuscript [Proving correctness for SQL implementations of OCL constraints](). The following show a sample single testcase:
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

### Running the tool

The script runs the benchmark for the given number of testcases.

For each testcase, the tool generates a MSFOL theory written in SMT2 file. 
The header for the SMT2 file is stored in the `output/header.smt2` file.
