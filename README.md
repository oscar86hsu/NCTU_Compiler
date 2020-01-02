# Project Assignment 5 - Code Generation

**Introduction to Compiler Design by Prof. Yi-Ping You**

Due Date: **23:59, January 15, 2020**

Your assignment is to generate `RISC-V instructions` for the **`P`** language based on the `AST` and `symbol table` that you have built in the previous assignments. The generated code will then be executed on a RISC-V simulator, called `Spike`.

---

**Table of Contents**
- [Project Assignment 5 - Code Generation](#project-assignment-5---code-generation)
  - [Assignment](#assignment)
  - [Generating RISC-V Instructions](#generating-risc-v-instructions)
    - [Initialization](#initialization)
    - [Declarations of Variables and Constants](#declarations-of-variables-and-constants)
    - [Expression](#expression)
    - [Function Declaration and Invocation](#function-declaration-and-invocation)
    - [Simple Statement](#simple-statement)
    - [Conditional Statement](#conditional-statement)
    - [For Statement and While Statement](#for-statement-and-while-statement)
  - [Implementation Hints](#implementation-hints)
  - [Project Structure](#project-structure)
  - [Assessment Rubrics (Grading)](#assessment-rubrics-grading)
  - [Build and Execute](#build-and-execute)
  - [Submitting the Assignment](#submitting-the-assignment)

---

## Assignment

In order to keep this assignment simple, only the `integer` type is needed to be implemented and the `array` type is not considered. Your assignment is to generate `RISC-V` instructions for a `P` program that contains any of the following constructs:

 - Global variable or local variable declaration.
 - Global constant or local constant declaration.
 - Function declaration.
 - Assign statement.
 - Simple statement.
 - Expressions with only `+` `-` (unary and binary) `*` `/` `mod` `function invocation` included.
 - Function invocation statement.
 - Conditional statement.
 - For statement and while statement.

The generated `RISC-V` instructions should be saved in a file with the same name as the input `P` file but with a `.s` extension. In addition, the file should be stored in a directory, which is set by the flag `--output_code_dir [output directory name]`. For example, the following command translates `./test.p` into `./output_riscv_code/test.s`.

```
./compiler test.p --output_code_dir output_riscv_code
```

## Generating RISC-V Instructions

 > In the following subsections, we provide some examples of how to translate a `P` construct into RISC-V instructions. You may design your own instruction selection rules, as long as the generated code does what it should do. We recommend you read the [`RISC-V` tutorial](RISC-V-tutorial) before getting into the following subsections.

The generated `RISC-V` code will have the following structure:

```assembly
.bss
    ; uninitialized global variable(s)

.text
    ; global constant(s)

.text
    ; function

.text
    ; main function
```

### Initialization

 - An empty `P` program

    ```p
    // test1.p
    test1;
    begin
    end
    end test1
    ```

    will be translated into the following `RISC-V` instructions.

    ```assembly
        .file "test1.p"
        .option nopic
    .text
        .align 2
        .global main       ; emit symbol 'main' to the global symbol table
        .type main, @function
    main:
        ; in the function prologue
        addi sp, sp, -64   ; move stack pointer to lower address to allocate a new stack
        sd ra, 56(sp)      ; save return address of the caller function in the current stack
        sd s0, 48(sp)      ; save frame pointer of the last stack in the current stack
        addi s0, sp, 64    ; move frame pointer to the bottom of the current stack

        ; in the function epilogue
        ld ra, 56(sp)      ; load return address saved in the current stack
        ld s0, 48(sp)      ; move frame pointer back to the bottom of the last stack
        addi sp, sp, 64    ; move stack pointer back to the top of the last stack
        jr ra              ; jump back to the caller function
        .size main, .-main 
    ```

A function `main` must be generated for the compound statement (program body) in the program node. 

You should allocate a local memory in the function prologue and clear the local memory in the function epilogue. In this assignment, allocate **64 bytes** of local memories is sufficient. However, in modern compilers, the size of the local memory depends on the demand of the function.

### Declarations of Variables and Constants

#### Global Variables

 - Declaring a global variable `a`

    ```p
    var a: integer;
    ```

    will be translated into the following `RISC-V` instructions.

    ```assembly
    .bss        ; emit bss section
    a:          ; emit symbol 'a' to the global symbol table
        .word 0 ; 32-bit word
    ```

 - Assigning a value to a global variable `a`

    ```p
    a := 4;
    ```

    will be translated into the following `RISC-V` instructions.

    ```
    li t0, 4     ; load value '4' to register 't0'
    la t1, a     ; load the address of variable 'a'
    sw t0, 0(t1) ; save the value to the address of 'a'
    ```

#### Local Variables

 - Declaring a local variable
   + Each local integer variable occupies four bytes of the allocated local memory. For example, `fp-16` to `fp-20` for variable `b` and `fp-20` to `fp-24` for variable `c`. This information should be stored in the `symbol table`.

 - Assigning a value to local variable `b` which is stored in `fp-16` to `fp-20`

    ```p
    var b, c: integer;
    b := 4;
    c := 6;
    ```

    will be translated into the following `RISC-V` instructions.

    ```assembly
    li t0, 4
    sw t0, -20(s0)   
    li t0, 6
    sw t0, -24(s0)  
    ```

#### Global Constants

 - Declaring a global constant `d`

    ```p
    var d: 4;
    ```

    will be translated into the following `RISC-V` instructions.

    ```assembly
    .text       ; emit text section
    d:          ; emit symbol 'd' to the global symbol table
        .word 4 
    ```

#### Local Constants

The same as local variables.

### Expression

Here is a simple method for translating an expression in terms of how you manage registers. When traversing to a `computation` node, (1) load the value of the child `variable reference` nodes to some registers (e.g., registers `t0` and `t1`), and (2) then compute the result with one or more instructions, and (3) finally save the result to a specific register that you choose (e.g., register `t0`). Consequently, when you traverse back to a parent node of the `computation` node, you can be sure that the result of the traversed `computation` node is saved in the specific register.
 
Consider an expression `a := (b + c) * d;`, where `a` is a global variable, `b` and `c` are local variables, and `d` is a global constant. Suppose the traversing order of the AST of this expression is `variable reference node a` -> `variable reference node b` -> `variable reference node c` -> `variable reference node d` -> `computation node` -> `computation node` -> `assignment node`. The process of translating the expression is given as follows.

<img src="./imgs/expression.png" width="650">

 - Adding up local variable `b` and local variable `c`, then multiplying with global constant `d`, and finally assigning to global variable `a`

    ```p
    a := (b + c) * d;
    ```

    will be translated into the following `RISC-V` instructions.

    ```assembly
    lw t0, -20(s0)  ; load the value of 'b'
    lw t1, -24(s0)  ; load the value of 'c'
    addw t2, t1, t0 ; b + c
    mv t0, t2       ; always move the value to a certain register you choose
    la t1, d        ; load the address of 'd'
    lw t2, 0(t1)    ; load the 32-bit value of 'd'
    mv t1, t2       ; always move the value to a certain register you choose
    mulw t2, t1, t0 ; (b + c) * d
    mv t0, t2       ; always move the value to a certain register you choose
    la t1, a        ; load the address of 'a'
    sw t0, 0(t1)    ; save the value to 'a'
    ```

### Function Declaration and Invocation

 - Declaring a function `sum`

    ```p
    sum(a,b: integer): integer;
    begin
        var c: integer;
        c := a + b;
        return c;
    end
    end sum
    ```

    will be translated into the following `RISC-V` instructions.

    ```assembly
    .text
        .align 2
        .global sum
        .type sum, @function
    sum:
        addi sp, sp, -64
        sd ra, 56(sp)
        sd s0, 48(sp)
        addi s0, sp, 64
        sw a0, -20(s0)  ; save parameter 'a' in the local stack
        sw a1, -24(s0)  ; save parameter 'b' in the local stack
        lw t0, -20(s0)  ; load the value of 'a'
        lw t1, -24(s0)  ; load the value of 'b'
        addw t2, t1, t0 ; a + b
        mv t0, t2       ; always move the value to a certain register you choose
        sw t0, -28(s0)  ; save the value to 'c'
        lw a0, -28(s0)  ; load the value of 'c' to the return value register 'a0'
        ld ra, 56(sp)
        ld s0, 48(sp)
        addi sp, sp, 64
        jr ra
        .size sum, .-sum
    ```

 - Call function `sum` with local variable `b` and global constant `d`, then assign the result to global variable `a`

    ```p
    a := sum(b, d);
    ```

    will be translated into the following `RISC-V` instructions.

    ```assembly
    lw a0, -20(s0) ; load the value of 'b' to the first argument register 'a0'
    la t1, d       ; load the address of 'd'
    lw a1, 0(t1)   ; load the 32-bit value of 'd' to the second argument register 'a1'
    jal ra, sum    ; call function 'sum'
    mv t0, a0      ; always move the return value to a certain register you choose
    la t1, a       ; load the address of 'a'
    sw t0, 0(t1)   ; save the value to 'a'
    ```

> Note that the function argument number in the test case may be larger than **eight**, and there are only `a0`-`a7` registers. You should try to place the remain arguments in other places.

### Simple Statement

It's a little complicated to call an `IO` system call, so we provide you a **print** function and a **read** function in `io.c`. You can compile and link your generated code with the functions by:

```
riscv64-unknown-elf-gcc [generated RISC-V assembly file] io.c -o [output ELF file] 
``` 

 - Printing a global variable `a`

    ```p
    print a;
    ```

    will be translated into the following `RISC-V` instructions.

    ```assembly
    la t0, a
    lw a0, 0(t0)    ; load the value of 'a' to the first argument register 'a0'
    jal ra, print   ; call function 'print'
    ```

 - Read a value and save to a global variable `a`

    ```p
    read a;
    ```

    will be translated into the following `RISC-V` instructions.

    ```assembly
    jal ra, read    ; call function 'read'
    la t0, a
    sw a0, 0(t0)    ; save the return value to 'a'
    ```

### Conditional Statement

 - Branching according to `a`'s value

    ```p
    if ( a <= 40 ) then  
        print a;
    else
        print b;
    end if
    ```

    will be translated into the following `RISC-V` instructions.

    ```assembly
        la t0, a
        lw t1, 0(t0)    ; load the value of 'a'
        mv t0, t1
        li t1, 40
        bgt t0, t1, L2  ; if a > 40, jump to L2
    L1:
        la t0, a
        lw a0, 0(t0)    ; load the value of 'a' to the first argument register 'a0'  
        jal ra, print   ; call function 'print'
        j L3            ; jump to L3
    L2:
        lw a0, -20(s0)  ; load the value of 'b' to the first argument register 'a0'  
        jal ra, print   ; call function 'print'
    L3:
    ```

### For Statement and While Statement

 - Looping until b >= 8

    ```p
    while b < 8 do
        print b;
        b := b + 1;
    end do
    ```

    will be translated into the following `RISC-V` instructions.

    ```assembly
        j L5            ; jump to L5
    L4:
        lw a0, -20(s0)  ; load the value of 'b' to the first argument register 'a0'
        jal ra, print   ; call function 'print'
        lw t0, -20(s0)  ; load the value of 'b'
        li t1, 1        
        addw t2, t1, t0 ; b = b + 1
        mv t0, t2
        sw t0, -20(s0)  ; save the value to 'b'
    L5: 
        lw t0, -20(s0)  ; load the value of 'b' 
        li t1, 8
        blt t0, t1, L4  ; if b < 8, jump to the loop content
    ```

### Combining all examples above

```p
// test1.p
test1;

var a: integer;
var d: 4;

sum(a,b: integer): integer;
begin
    var c: integer;
    c := a + b;
    return c;
end
end sum

begin

var b, c: integer;
b := 4;
c := 6;

read a;
print a;

a := sum(b, d);
print a;

a := (b + c) * d;
print a;

if ( a <= 40 ) then  
    print a;
else
    print b;
end if

while b < 8 do
    print b;
    b := b + 1;
end do

end
end test1
```

will be translated into the following `RISC-V` instructions.

```assembly
    .file "test1.p"
    .option nopic
.bss
a:
    .word 0  
.text
d:
    .word 4
.text
    .align 2
    .global sum
    .type sum, @function
sum:
    addi sp, sp, -64
    sd ra, 56(sp)
    sd s0, 48(sp)
    addi s0, sp, 64
    sw a0, -20(s0)
    sw a1, -24(s0)
    lw t0, -20(s0)
    lw t1, -24(s0)
    addw t2, t1, t0
    mv t0, t2
    sw t0, -28(s0)
    lw a0, -28(s0)
    ld ra, 56(sp)
    ld s0, 48(sp)
    addi sp, sp, 64
    jr ra
    .size sum, .-sum
.text
    .align 2
    .global main
    .type main, @function
main:
    addi sp, sp, -64
    sd ra, 56(sp)
    sd s0, 48(sp)
    addi s0, sp, 64
    li t0, 4
    sw t0, -20(s0)  
    li t0, 6
    sw t0, -24(s0) 
    jal ra, read
    la t0, a
    sw a0, 0(t0)
    la t0, a
    lw a0, 0(t0)
    jal ra, print
    lw a0, -20(s0)
    la t1, d
    lw a1, 0(t1)
    jal ra, sum
    mv t0, a0
    la t1, a
    sw t0, 0(t1)
    la t0, a
    lw a0, 0(t0)
    jal ra, print
    lw t0, -20(s0) 
    lw t1, -24(s0)
    addw t2, t1, t0
    mv t0, t2
    la t1, d
    lw t2, 0(t1)
    mv t1, t2
    mulw t2, t1, t0
    mv t0, t2
    la t1, a
    sw t0, 0(t1)
    la t0, a
    lw a0, 0(t0)
    jal ra, print
    la t0, a
    lw t1, 0(t0)
    mv t0, t1
    li t1, 40
    bgt t0, t1, L2
L1:
    la t0, a
    lw a0, 0(t0)
    jal ra, print
    j L3
L2:
    lw a0, -20(s0) 
    jal ra, print
L3:
    j L5
L4:
    lw a0, -20(s0)
    jal ra, print
    lw t0, -20(s0)
    li t1, 1        
    addw t2, t1, t0
    mv t0, t2
    sw t0, -20(s0)
L5: 
    lw t0, -20(s0)
    li t1, 8
    blt t0, t1, L4
    ld ra, 56(sp)
    ld s0, 48(sp)
    addi sp, sp, 64
    jr ra
    .size main, .-main
```

## Implementation Hints

### Using `C` compiler that targets RISC-V

If you have no idea what instructions will be generated from a `P` program, you may write a corresponding `C` program and run the following command to generate `RISC-V` instructions using a `C` compiler. Check out `[output assembly file]` to see what instructions were generated.

```
riscv64-unknown-elf-gcc -c -S [input C file] -o [output assembly file]
```

## Project Structure

- `README.md`
- /src
    - Makefile
    - `scanner.l`
    - `parser.y`
    - /include
        - /AST
        - /semantic
        - /visitor
        - Other modules you may add
    - /src
        - /AST
        - /semantic
        - /visitor
        - Other modules you may add
    - Other modules you may add
- /src-c
	- Sample code of hw4 in C
- /src-cpp
	- Sample code of hw4 in C++ (credit: @allen880117)
- /report
    - `README.md`

In this assignment, you have to do the following tasks:

- Revise `ast.h` and `ast.c`, and add some modules (e.g., `codegen.h` and `codegen.c`) to generate the `RISC-V` instructions.
- Write the report in `report/README.md`. The report should describe your feedback about `hw5` For example, is the spec and the tutorial clear? Is `hw5` too easy?

If you want to preview your report in GitHub style markdown before pushing to GitHub, [`grip`](https://github.com/joeyespo/grip) might be the tool you need.

## Assessment Rubrics (Grading)

Total of 125 points.

+ Passing all test cases we provided (60 pts)
+ Passing all hidden test cases (35 pts)
+ **Demo (10 pts)**
+ Report (5 pts)
+ Bonus (Total of 15 pts)
  + Code generation for array types (3 pts)
  + Code generation for Boolean types (3 pts)
  + Code generation for string types (4 pts)
  + Code generation for real types (5 pts)
  
> Notice that 
> 
> 1. If you are not able to attend the demo and your request for leave is not approved, we won't conduct the hidden test cases for your assignment.
> 
> 2. The code generation for additional types will be tested with expressions and functions, not just declarations.

## Build and Execute

- Build: `cd src && make clean && make`
- Execute: `./compiler [input file] --output_code_dir [output directory name]`
- Test: `cd test && python3 test.py`

### Build Project

TA would use `src/Makefile` to build your project by simply typing `make clean && make` on the CS workstation. You have to make sure that it will generate an executable named '`compiler`'. **No further grading will be made if the `make` process fails or the executable '`compiler`' is not found.**

### Test your compiler

We provide some basic tests in the test folder. Simply `cd` to test folder and type `python3 test.py` to test your compiler. You can also type `python3 test.py --help` to know what arguments you can set.

The objective we provide sample test cases is making sure your compiler generates the instructions correctly. You will get at least **60 pts** if you pass all the test cases.

Please use `student_` as the prefix of your own tests to prevent TAs from overriding your files. For example: `student_identifier_test`.

### Simulator Commands

The `RISC-V` simulator has been installed in the CS workstation. You may install it on your environment. The following commands show how to generate the executable and run the executable on the `RISC-V` simulator. 

 - Compile the generated `RISC-V` instructions to the `Executable and Linkable Format (ELF)` file.

```
riscv64-unknown-elf-gcc -o [output ELF file] [input RISC-V instruction file]
```

 - Run the `ELF` file on the simulator `spike`.

```
spike pk [ELF file]
```

## Submitting the Assignment

You should push all your commits to the designated repository (hw5-\<Name of your GitHub account\>) under the compiler-f19 GitHub organization by the deadline (given in the very beginning of this assignment description).
At any point, you may save your work and push commits to your repository. You **must** commit your final version to the **master branch**, and we will grade the commit which is last pushed on your master branch. The **push time** of that commit will be your submission time, so you should not push any commits to the master branch after the deadline if you have finished your assignment; otherwise, you will get a late penalty.

Note that the penalty for late homework is **15% per day** (weekends count as 1 day). Late homework will not be accepted after sample codes have been posted.

In addition, homework assignments **must be individual work**. If we detect what we consider to be intentional plagiarism in any assignment, the assignment will receive reduced or, usually, **zero credit**.
