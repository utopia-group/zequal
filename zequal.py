#!/usr/bin/env python3

from enum import Enum
from glob import glob
import subprocess
import argparse
import sys
import os
import time
import signal
from collections import namedtuple

CUR_DIR = os.path.dirname(os.path.abspath(__file__))
ZKVERIFIER = f"{CUR_DIR}/target/debug/verify"

VerifierArgs = namedtuple("VerifierArgs", ("noSA", "onlySA", "safeInvocations", "createCSV"))

class VerificationResult(Enum):
    VERIFIED = 1
    NOT_VERIFIED = 2
    CRASH = 3
    TIMEOUT = 4
    NOT_FOUND = 5


def runBenchmark(benchmark, timeout, output, verifierArgs):
    if not os.path.exists(benchmark) or not os.path.isfile(benchmark):
        return VerificationResult.NOT_FOUND

    start = time.time()

    execCmd = [ZKVERIFIER, "--use-z3"]
    if verifierArgs.noSA:
        execCmd.append("--no-static-analysis")
    if verifierArgs.onlySA:
        execCmd.append("--only-static-analysis")
    if verifierArgs.safeInvocations:
        execCmd.append("--assume-safe-invocations")
    execCmd.append(benchmark)

    verifierExec = subprocess.Popen(execCmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)

    try:
        (stdout, stderr) = verifierExec.communicate(timeout=timeout)
        exec_time = time.time() - start

        if output:
            file = open(output, "w")
            file.write(stdout)
            file.write(stderr)
            file.close()

        if "Verified Equivalence" in stdout:
            return VerificationResult.VERIFIED, exec_time
        elif "Verification Failed" in stdout:
            return VerificationResult.NOT_VERIFIED, exec_time
        else:
            return VerificationResult.CRASH, exec_time
    except KeyboardInterrupt:
        os.killpg(verifierExec.pid, signal.SIGTERM)
        if output:
            (stdout, stderr) = verifierExec.communicate()
            file = open(output, "w")
            file.write(stdout)
            file.write(stderr)
            file.write(f"TIMEOUT after {timeout} seconds")
            file.close()
    except subprocess.TimeoutExpired:
        os.killpg(verifierExec.pid, signal.SIGTERM)
        if output:
            (stdout, stderr) = verifierExec.communicate()
            file = open(output, "w")
            file.write(stdout)
            file.write(stderr)
            file.write(f"TIMEOUT after {timeout} seconds")
            file.close()

        return VerificationResult.TIMEOUT, timeout

def runBenchmarks(benchmarks, timeout, outputDir, verifierArgs):
    if outputDir:
        if os.path.exists(outputDir):
            if not os.path.isdir(outputDir):
                sys.exit("The specified output location is not a directory")
        else:
            os.makedirs(outputDir)

    csvFile = None
    if verifierArgs.createCSV:
        outputFilename = "results.csv"
        if outputDir:
            outputFilename = os.path.join(outputDir, outputFilename)

        csvFile = open(outputFilename, "w")
        csvFile.write(f"Benchmark,Status,Time\n")


    longestBenchmarkName = max([len(b) for b in benchmarks])
    nameColumnLen = max([longestBenchmarkName, 4])
    statusColumnLen = 12
    timeColumnLen = 10

    centeredName = "Name".center(nameColumnLen)
    centeredStatus = "Status".center(statusColumnLen)
    centeredTime = "Time (s)".center(timeColumnLen)
    print(f"| {centeredName} | {centeredStatus} | {centeredTime} |")
    print(f"| :{'-' * (nameColumnLen - 2)}: | :{'-' * (statusColumnLen - 2)}: | :{'-' * (timeColumnLen - 2)}: |")
        
    for benchmark in benchmarks:
        output = None

        if outputDir:
            basename = os.path.basename(benchmark)
            (base, _) = os.path.splitext(basename)
            output = f"{args.output}/{base}.out"


        result, execTime = runBenchmark(benchmark, timeout, output, verifierArgs)

        timeStr = f"{execTime:.3f}"
        print(f"| {benchmark.center(nameColumnLen)} | {result.name.center(statusColumnLen)} | {timeStr.center(timeColumnLen)} |")
        if csvFile:
            csvFile.write(f"{benchmark},{result.name},{timeStr}\n")

    if csvFile:
        csvFile.close()

parser = argparse.ArgumentParser(prog='zequal', description='Verifies the equivalence of a ZK circuit', add_help=True)
parser.add_argument("-o", "--output", help="Output verifier output in the given directory")
parser.add_argument("-t", "--timeout", type=int, default=600, help="Verifier timeout in seconds")
parser.add_argument("-nsa", "--no-static-analysis", action='store_true', default=False, help="Perform verification without static analysis")
parser.add_argument("-ic", "--infer-contract", action='store_true', default=False, help="(Unstable) Attempt to infer method contracts for invoked circuits")
parser.add_argument("-osa", "--only-static-analysis", action='store_true', default=False, help="Perform verification only with static analysis")
parser.add_argument("-csv", "--output-csv", action='store_true', default=False, help="Output results as a CSV")
parser.add_argument("filenames", nargs='+', help="One or more circom files to verify")
args = parser.parse_args()
filenames = [f for l in args.filenames for f in glob(l)]
verifierArgs = VerifierArgs(args.no_static_analysis, args.only_static_analysis, not args.infer_contract, args.output_csv)
runBenchmarks(filenames, args.timeout, args.output, verifierArgs)


