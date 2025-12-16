# CS 6335 -- `atoi` Proof of Correctness

## Prerequisites
The layout and build scripts of this project assumes that...
1. You are running **Coq 8.20**. If you are running a higher version, there is no guarantee that the build script will work, as the Picinae build scripts also assume the working version of Coq is 8.20.
2. `coqc` in your `PATH` - Add Coq's `bin` directory to your system `PATH` environment variable.
    - **Suggested Approach**: *Add a new System Environment variable named `COQ_HOME` and set it to the path of your Coq installation. Then, within the `PATH` environment variable, add a new entry named `%COQ_HOME%\bin`. This will allow you to run any of the Coq executables from the command line (which is required for the build script).*
    - After adding the `PATH` variable, you can verify that your setup is correct by opening a new terminal and running the command `coqc -v` in the command line. If you see the version of Coq that you are expecting, then your setup is correct.

## Setup & Build (Windows)

1. **First-time setup** (initializes submodules and builds Picinae):
   ```powershell
   .\first_time_setup.bat
   ```
   - Picinae is included as a git submodule. `first_time_setup.bat` runs `git submodule update --init --recursive` to fetch the submodule and then builds the Picinae sources.
   - We require that an updated version of Picinae (not yet merged into master) is used due to a state explosion bug in the `step` tactic in the current version of Picinae. This script handles the process of copying the updated Picinae files into the project directory, and then building the Picinae source files.
   - The `windows_build.bat` script within Picinae assumes that you have installed Coq to the location `C:\Coq`. If you have installed Coq to a different location, you will need to modify the `windows_build.bat` script within the `Picinae` directory to point to your Coq installation location.
   - If your Coq installation is in a different location, then you will need to run `first_time_setup.bat` twice: once to clone Picinae, and then again to build Picinae (after you have modified the `windows_build.bat` script).

2. **Build the atoi proof** (only non-Picinae files):
   ```powershell
   .\windows_build.bat
   ```

3. **Clean compiled files** (preserves Picinae):
   ```powershell
   .\clean.bat
   ```
## Setup & Build (Linux)

1. Copy the updated Picinae files into the Picinae git submodule project directory.
2. Run make. The makefile supports build targets **all** and **clean**.

## Project Structure
```
├── Picinae/                      Picinae is a git submodule (master branch of the upstream repo)
├── LiftedSource/                 Lifted source file(s) provided by CS 6335 Staff
│   └── atoi_lo_atoi_armv8.v
├── Report/                       All report-related artifacts
├── Proofs/                       Correctness proof for atoi
│   ├── Helpers/                  Supporting helper files for the main proof
│   │   ├── BitWidth.v            Helpers relating to determining the bit width of an integer
│   │   ├── Digits.v              Helpers relating to character to digit manipulation
│   │   ├── Invariants.v          Helpers defining and working with invariants
│   │   ├── MainProofHelpers.v    Supporting lemmas and tactics for the main proof
│   │   ├── Sign.v                Helpers relating to sign detection
│   │   ├── Specification.v       Defines the "trusted" specification of atoi 
│   │   ├── SpecificationProof.v  Proofs of properties about the specification
│   │   └── Whitespace.v          Helpers relating to leading whitespace character detection
│   └── Main_Proof.v              Main proof file
├── _CoqProject                   Coq project configuration
├── clean.bat
├── first_time_setup.bat
└── windows_build.bat
```

## Notes
- All `.v` files in `LiftedSource/` and `Proofs/` are automatically discovered and compiled
- To add new helpers, simply create `.v` files in `Proofs/Helpers/`. Then update the `_CoqProject` file and the `windows_build.bat` script to include the new files.
- To clean Picinae separately, run `cd Picinae` then `.\clean.bat` (Picinae contains its own clean script).
- If you are having an issue with the source files not properly recognizing the imports, reload your VSCode or IDE window. For VSCode, you can do this by pressing `Ctrl+Shift+P` and then typing `Developer: Reload Window`.

## Acknowledgements
The project was completed, in whole, by "the authors": Matthew Sheldon, Isabella Pereira, Jarrod Rogers, Naja-Lee Habboush, and Brandon Wang. This includes all proof source code as well as the build scripts. The project was completed as part of the "Language-Based Security" course at the University of Texas at Dallas, taught by Dr. Kevin Hamlen during the Fall 2025 semester.
