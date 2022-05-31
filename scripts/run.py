#!/usr/bin/env python3
"""
@author: Anonymous Author(s)

"""
import argparse
import os
import shutil
import subprocess
import sys
import signal
import configparser as ConfigParser
import json

BASE_DIRECTORY = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

print("Running integration with root directory " + BASE_DIRECTORY)

class JSONObject(object):
    def __init__(self, d):
        self.__dict__ = d


def build(conf, skip_tests=False):
    """
    Builds all solutions
    """
    tools = [conf.OCL2MSFOL, conf.SQL2MSFOL]
    for tool in tools:
        config = ConfigParser.ConfigParser()
        config.read(os.path.join(BASE_DIRECTORY, "tools", tool, "solution.ini"))
        set_working_directory("tools", tool)
        if skip_tests:
            subprocess.check_call(config.get('build', 'skipTests'), shell=True)
        else:
            subprocess.check_call(config.get('build', 'default'), shell=True)


def run(conf):
    """
    Integration
    """
    datamodel = os.path.join(BASE_DIRECTORY, "resources", conf.Datamodel)
    os.environ['DM'] = os.path.abspath(datamodel)
    ocl2msfol = conf.OCL2MSFOL
    ocl2msfol_config = ConfigParser.ConfigParser()
    ocl2msfol_config .read(os.path.join(BASE_DIRECTORY, "tools", ocl2msfol, "solution.ini"))
    sql2msfol = conf.SQL2MSFOL
    sql2msfol_config = ConfigParser.ConfigParser()
    sql2msfol_config .read(os.path.join(BASE_DIRECTORY, "tools", sql2msfol, "solution.ini"))
    for iTestcase, testcase in enumerate(conf.Testcases):
        print("Generating theory for testcase {0}".format(str(iTestcase)))
        ctx = ''
        for var in testcase.context:
            if ctx == '':
                ctx += '{0}:{1}'.format(var.name, var.type)
            else:
                ctx += ',{0}:{1}'.format(var.name, var.type)
        if ctx != '':
            os.environ['CTX'] = ctx
        inv = ''
        for invariant in testcase.invariants:
            if inv == '':
                inv += invariant
            else:
                inv += ','+invariant
        if inv != '':         
            os.environ['INV'] = inv
        os.environ['OCL'] = testcase.OCL
        os.environ['SQL'] = testcase.SQL
        filename = 'output{0}'.format(str(iTestcase))
        os.environ['FILE'] = filename
        header = os.path.join(BASE_DIRECTORY, "output", "header.smt2")
        result_file = os.path.join(BASE_DIRECTORY, "output", filename + ".smt2")
        if os.path.exists(result_file):
            os.remove(result_file)
        shutil.copy(header, result_file)

        set_working_directory("tools", ocl2msfol)
        with subprocess.Popen(ocl2msfol_config.get('run', 'cmd'), shell=True, stdout=subprocess.PIPE,
                            start_new_session=True) as process:
            try:
                stdout, stderr = process.communicate(timeout=conf.Timeout)
                return_code = process.poll()
                if return_code:
                    raise subprocess.CalledProcessError(return_code, process.args,
                                                        output=stdout, stderr=stderr)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGINT)  # send signal to the process group
                raise

        ocl_formula = stdout
        ocl_theory_file = os.path.join(BASE_DIRECTORY, "tools", ocl2msfol, filename)
        with open(ocl_theory_file,'r') as sourcefile, open(result_file,'a') as targetfile:
            for line in sourcefile:
                targetfile.write(line)
        os.remove(ocl_theory_file)

        set_working_directory("tools", sql2msfol)
        with subprocess.Popen(sql2msfol_config.get('run', 'cmd'), shell=True, stdout=subprocess.PIPE,
                            start_new_session=True) as process:
            try:
                stdout, stderr = process.communicate(timeout=conf.Timeout)
                return_code = process.poll()
                if return_code:
                    raise subprocess.CalledProcessError(return_code, process.args,
                                                        output=stdout, stderr=stderr)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGINT)  # send signal to the process group
                raise
        with open(result_file, "ab") as file:
            file.write(stdout)

        # Adding proof goals
        set_working_directory("output")
        proofgoal = "(assert (not (exists ((x Int)) (and (index0 x) (forall ((y Int)) (=> (not (= x y)) (not (index0 y))))))))\r\n"  
        proof_file1 = filename + '-C1.smt2'
        shutil.copy(result_file, proof_file1)
        with open(proof_file1, "ab") as file:
            file.write(proofgoal.encode())
            file.write("(check-sat)\r\n".encode())

        negate_proofgoal_ocl = "(assert (not {0}))\r\n".format(ocl_formula.decode("utf-8").replace("\r\n","")) 
        proofgoal_sql = "(assert (forall ((x Int)) (=> (index0 x) (= (val-index0-res x) TRUE))))\r\n"
        proof_file2 = filename + '-C2.smt2'
        shutil.copy(result_file, proof_file2)
        with open(proof_file2, "ab") as file:
            file.write(negate_proofgoal_ocl.encode())
            file.write(proofgoal_sql.encode())
            file.write("(check-sat)\r\n".encode())

        proofgoal_ocl = "(assert {0})\r\n".format(ocl_formula.decode("utf-8").replace("\r\n","")) 
        negate_proofgoal_sql = "(assert (not (forall ((x Int)) (=> (index0 x) (= (val-index0-res x) TRUE)))))\r\n"
        proof_file3 = filename + '-C3.smt2'
        shutil.copy(result_file, proof_file3)
        with open(proof_file3, "ab") as file:
            file.write(proofgoal_ocl.encode())
            file.write(negate_proofgoal_sql.encode())
            file.write("(check-sat)\r\n".encode())

def clean_dir(*path):
    dir = os.path.join(BASE_DIRECTORY, *path)
    if os.path.exists(dir):
        shutil.rmtree(dir)
    os.mkdir(dir)


def set_working_directory(*path):
    dir = os.path.join(BASE_DIRECTORY, *path)
    os.chdir(dir)


def visualize():
    """
    Visualizes the benchmark results
    """
    clean_dir("diagrams")
    set_working_directory("reporting2")
    subprocess.call(["Rscript", "-e", "rmarkdown::render('report.Rmd', output_format=rmarkdown::pdf_document())"])


def check_results():
    """
    Checks the benchmark results
    """
    clean_dir("results")
    set_working_directory("reporting")
    subprocess.call(["Rscript", "check_results.R"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("-b", "--build",
                        help="build the project",
                        action="store_true")
    parser.add_argument("-r", "--run",
                        help="run the integration",
                        action="store_true")
    parser.add_argument("-s", "--skip-tests",
                        help="skip tests",
                        action="store_true")
    parser.add_argument("-v", "--visualize",
                        help="create visualizations",
                        action="store_true")
    parser.add_argument("-t", "--test",
                        help="run test",
                        action="store_true")
    parser.add_argument("-d", "--debug",
                        help="set debug to true",
                        action="store_true")
    parser.add_argument('-c', '--testcase', 
                        action='store', 
                        dest='testcase', 
                        help='The testcase filename.')
    args = parser.parse_args()

    FILE_NAME = args.testcase

    set_working_directory("config")
    with open(FILE_NAME+".json", "r") as config_file:
        config = json.load(config_file, object_hook=JSONObject)

    # if there are no args, execute a full sequence
    # with the test and the visualization/reporting
    no_args = all(not val for val in vars(args).values())

    if args.debug:
        os.environ['DEBUG'] = 'true'
    if args.build or args.test or no_args:
        build(config, args.skip_tests and not args.test)
    if args.run or no_args:
        run(config)
    # not yet supported!
    if args.visualize or no_args:
        visualize() 
