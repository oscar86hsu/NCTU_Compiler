#!/usr/bin/env python3

import subprocess
import os
import shutil
import sys
from argparse import ArgumentParser

class Colors:
    YELLOW = '\033[33m'
    BLUE = '\033[96m'
    GREEN = '\033[92m'
    RED = '\033[91m'

class Grader:
    sample_solution_dir = "./sample-solutions"
    test_case_dir = "./test-cases"
    test_cases = {
        1 : "variableConstant",
        2 : "expression",
        3 : "function",
        4 : "specExample",
        5 : "condition",
        6 : "loop"
    }
    case_id_list = test_cases.keys()

    def __init__(self, compiler, output_code_dir, executable_file_dir, code_result_dir):
        self.compiler = compiler

        self.output_code_dir = output_code_dir
        if not os.path.exists(self.output_code_dir):
            os.makedirs(self.output_code_dir)

        self.executable_file_dir = executable_file_dir
        if not os.path.exists(self.executable_file_dir):
            os.makedirs(self.executable_file_dir)

        self.code_result_dir = code_result_dir
        if not os.path.exists(self.code_result_dir):
            os.makedirs(self.code_result_dir)

    def gen_riscv_code(self, case_id):
        test_case = "%s/%s.p" % (self.test_case_dir, self.test_cases[case_id])
      
        clist = [self.compiler, test_case, "--output_code_dir", self.output_code_dir]
        cmd = " ".join(clist)
        try:
            proc = subprocess.Popen(cmd, shell=True)
        except Exception as e:
            print(Colors.RED + "Call of '%s' failed: %s" % (" ".join(clist), e))
            exit(1)

        proc.wait()

    def compile_riscv_code(self, case_id):
        test_case = "%s/%s.s" % (self.output_code_dir, self.test_cases[case_id])
        executable_file = "%s/%s" % (self.executable_file_dir, self.test_cases[case_id])

        clist = ["riscv64-unknown-elf-gcc", test_case, "io.c", "-o", executable_file]
        cmd = " ".join(clist)
        try:
            proc = subprocess.Popen(cmd, shell=True)
        except Exception as e:
            print(Colors.RED + "Call of '%s' failed: %s" % (" ".join(clist), e))
            exit(1)

        proc.wait()

    def run_riscv_code(self, case_id):
        output_file = "%s/%s" % (self.code_result_dir, self.test_cases[case_id])
        executable_file = "%s/%s" % (self.executable_file_dir, self.test_cases[case_id])

        clist = ["echo", "123", "|", "spike", "pk", executable_file]
        cmd = " ".join(clist)
        try:
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
        except Exception as e:
            print(Colors.RED + "Call of '%s' failed: %s" % (" ".join(clist), e))
            exit(1)

        stdout = str(proc.stdout.read(), "utf-8")
        stderr = str(proc.stderr.read(), "utf-8")
        proc.wait()

        with open(output_file, "w") as out:
            out.write(stdout)
            out.write(stderr)

    def compare_file_content(self, case_id):
        output_file = "%s/%s" % (self.code_result_dir, self.test_cases[case_id])
        solution = "%s/%s" % (self.sample_solution_dir, self.test_cases[case_id])

        ok = True
        sample_content = []
        output_content = []
        line_num = 0
        diff_output = []

        with open(solution, 'r') as f:
            for line in f:
                sample_content.append(line)
        with open(output_file, 'r') as f:
            for line in f:
                output_content.append(line)

        for line1, line2 in zip(sample_content, output_content):
            line_num += 1
            if line1.rstrip() !=  line2.rstrip():
                ok = False
                diff_output.append(["Difference found in line %d" % line_num, 
                                    "sample: " + line1.rstrip('\n'),
                                    "yours:  " + line2.rstrip('\n')])

        if len(sample_content) > line_num:
            ok = False
            for idx in range(line_num, len(sample_content)):
                diff_output.append(["Difference found in line %d" % (idx+1), 
                                    "sample: " + sample_content[idx].rstrip('\n'),
                                    "yours:"])
        if len(output_content) > line_num:
            ok = False
            for idx in range(line_num, len(output_content)):
                diff_output.append(["Difference found in line %d" % (idx+1), 
                                    "sample:",
                                    "yours:  " + output_content[idx].rstrip('\n')])

        return ok, diff_output
    
    def test_sample_case(self, case_id):
        self.gen_riscv_code(case_id)
        self.compile_riscv_code(case_id)
        self.run_riscv_code(case_id)

        return self.compare_file_content(case_id)

    def run(self):
        for b_id in self.case_id_list:
            c_name = self.test_cases[b_id]
            ok, diff_output = self.test_sample_case(b_id)
            if ok:
                print(Colors.YELLOW + "Running test case: " + Colors.BLUE + c_name + "  ==>  " + Colors.GREEN + "Pass!")
            else:
                print(Colors.YELLOW + "Running test case: " + Colors.BLUE + c_name + "  ==>  " + Colors.RED + "Fail!")
                for output in diff_output:
                    print(Colors.RED + output[0])
                    print(Colors.BLUE + output[1])
                    print(Colors.GREEN + output[2])

def main():
    parser = ArgumentParser()
    parser.add_argument("--compiler", help="Your compiler to test.", 
                                    default="../src/compiler")
    parser.add_argument("--output_code_dir", help="Directory that stores the output risc-v instructions of your compiler.", 
                                        default="./output_riscv_code")
    parser.add_argument("--executable_file_dir", help="Directory that stores the compiled executable files.", 
                                        default="./executable")
    parser.add_argument("--code_result_dir", help="Directory that stores the output content of your generated risc-v instructions.", 
                                        default="./code_executed_result")
    args = parser.parse_args()

    g = Grader(compiler = args.compiler, 
                output_code_dir = args.output_code_dir,
                executable_file_dir = args.executable_file_dir,
                code_result_dir = args.code_result_dir)
    g.run()

if __name__ == "__main__":
    main()
