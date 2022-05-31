#!/usr/bin/env python3
"""
@author: Anonymous Author(s)

"""
import argparse
from datetime import datetime
import os
import shutil
import subprocess
import signal
import configparser as ConfigParser
import json
from time import sleep
from logger import LOGGER, SGM

from numpy import true_divide

BASE_DIRECTORY = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROOF_GOAL_1 = "(assert (not (exists ((x Int)) (and (index0 x) (forall ((y Int)) (=> (not (= x y)) (not (index0 y))))))))\r\n"
PROOF_GOAL_2_OCL = "(assert (not {0}))\r\n"
PROOF_GOAL_2_SQL = "(assert (forall ((x Int)) (=> (index0 x) (= (val-index0-res x) TRUE))))\r\n"
PROOF_GOAL_3_OCL = "(assert {0})\r\n"
PROOF_GOAL_3_SQL = "(assert (not (forall ((x Int)) (=> (index0 x) (= (val-index0-res x) TRUE)))))\r\n"

print("Running integration with root directory " + BASE_DIRECTORY)

class JSONObject(object):
    def __init__(self, d):
        self.__dict__ = d


def build(conf):
    """
    Builds all solutions
    """
    tools = [conf.OCL2MSFOL, conf.SQL2MSFOL]
    for tool in tools:
        config = ConfigParser.ConfigParser()
        config.read(os.path.join(BASE_DIRECTORY, "tools", tool, "solution.ini"))
        set_working_directory("tools", tool)
        subprocess.check_call(config.get('build', 'default'), shell=True)


def run(conf):
    """
    Integration
    """
    start_time = datetime.today()
    LOGGER.run_start(len(conf.Testcases), start_time)
    datamodel = os.path.join(BASE_DIRECTORY, "resources", conf.Datamodel)
    os.environ['DM'] = os.path.abspath(datamodel)
    for iTestcase, testcase in enumerate(conf.Testcases):
        LOGGER.begin_proving_round(iTestcase)
        LOGGER.print_stat()
        filename = setting_ENV_variables(testcase, iTestcase)

        header = os.path.join(BASE_DIRECTORY, "output", "header.smt2")

        core_theory_filename = os.path.join(BASE_DIRECTORY, "output", filename + ".smt2")
        if os.path.exists(core_theory_filename):
            os.remove(core_theory_filename)
        shutil.copy(header, core_theory_filename)

        if 'cvc4' == SOLVER:
            cvc4_fragment = '(set-logic UFSLIA)\r\n'
            with open(core_theory_filename, "ab") as file:
                file.write(cvc4_fragment.encode())

        ocl_formula = ocl2msfol(conf, core_theory_filename, filename)
        sql2msfol(conf, core_theory_filename)

        # Adding proof goals
        set_working_directory("output")
        add_proof_goal(conf, [PROOF_GOAL_1], filename, core_theory_filename, 1)
        add_proof_goal(conf, [PROOF_GOAL_2_OCL.format(ocl_formula), PROOF_GOAL_2_SQL], filename, core_theory_filename, 2)
        add_proof_goal(conf, [PROOF_GOAL_3_OCL.format(ocl_formula), PROOF_GOAL_3_SQL], filename, core_theory_filename, 3)
    LOGGER.finish()

def setting_ENV_variables(testcase, iTestcase):
    ctx = ''
    for var in testcase.context:
        if ctx == '': ctx += '{0}:{1}'.format(var.name, var.type)
        else: ctx += ',{0}:{1}'.format(var.name, var.type)
    if ctx != '':  os.environ['CTX'] = ctx
    inv = ",". join(testcase.invariants)
    if inv != '': os.environ['INV'] = inv
    os.environ['OCL'] = testcase.OCL
    os.environ['SQL'] = testcase.SQL
    filename = 'output{0}'.format(str(iTestcase))
    os.environ['FILE'] = filename
    return filename

def ocl2msfol(conf, core_filename, filename):
    ocl2msfol = conf.OCL2MSFOL
    set_working_directory("tools", ocl2msfol)
    ocl2msfol_config = ConfigParser.ConfigParser()
    ocl2msfol_config.read(os.path.join(BASE_DIRECTORY, "tools", ocl2msfol, "solution.ini"))
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
    with open(ocl_theory_file,'r') as sourcefile, open(core_filename,'a') as targetfile:
        for line in sourcefile:
            targetfile.write(line)
    os.remove(ocl_theory_file)
    return ocl_formula.decode("utf-8").replace("\r\n","").replace("\n","")


def sql2msfol(conf, filename):
    sql2msfol = conf.SQL2MSFOL
    set_working_directory("tools", sql2msfol)
    sql2msfol_config = ConfigParser.ConfigParser()
    sql2msfol_config .read(os.path.join(BASE_DIRECTORY, "tools", sql2msfol, "solution.ini"))
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
    with open(filename, "ab") as file:
        file.write(stdout)
        file.close()

def add_proof_goal(conf, proofgoals, filename, corefile, id):
    filename = filename + '-C{0}.smt2'.format(str(id))
    shutil.copy(corefile, filename)
    with open(filename, "ab") as file:
        for proofgoal in proofgoals:
            file.write(proofgoal.encode())
        file.write("(check-sat)\r\n".encode())
        file.close()
    if SOLVER == 'cvc4':
        cvc4_checksat(conf, filename, id)
    else:
        z3_checksat(conf, filename, id)


def cvc4_checksat(conf, filename, id):
    with subprocess.Popen(['cvc4 ' + filename], shell=True, stdout=subprocess.PIPE,
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
    result = stdout.decode("utf-8").replace("\r\n","").replace("\n","")
    if result == 'unsat': 
        SGM.update_status(id, True)
    else: 
        SGM.update_status(id, False)
    SGM.current_subgoal += 1
    LOGGER.print_stat()


def z3_checksat(conf, filename, id):
    with subprocess.Popen(['z3 ' + filename], shell=True, stdout=subprocess.PIPE,
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
    result = stdout.decode("utf-8").replace("\r\n","").replace("\n","")
    if result == 'unsat': 
        SGM.update_status(id, True)
    else: 
        SGM.update_status(id, False)
    SGM.current_subgoal += 1
    LOGGER.print_stat()


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
    parser.add_argument('-c', '--testcase', 
                        action='store', 
                        dest='testcase', 
                        help='The testcase filename.')
    parser.add_argument('-s', '--solver', 
                        action='store', 
                        dest='solver', 
                        default='z3',
                        help='The solver of choice.')
    parser.add_argument('--get-model',
                        action='store_true',
                        dest='model',
                        help='get model when the proofgoal is unsuccessful')
    args = parser.parse_args()

    FILE_NAME = args.testcase
    SOLVER = args.solver

    set_working_directory("config")
    with open(FILE_NAME+".json", "r") as config_file:
        config = json.load(config_file, object_hook=JSONObject)

    # if there are no args, execute a full sequence
    # with the test and the visualization/reporting
    no_args = all(not val for val in vars(args).values())

    if args.build or no_args:
        build(config)
    if args.run or no_args:
        run(config)
