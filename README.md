# CS 6335 -- `atoi` Proof of Correctness

## Prerequisites
The layout and build scripts of this project assumes that...
1. You are running **Coq 8.20**. If you are running a higher version, there is no guarantee that the build script will work, as the Picinae build scripts also assume the working version of Coq is 8.20.
2. `coqc` in your `PATH` - Add Coq's `bin` directory to your system `PATH` environment variable.
    - **Suggested Approach**: *Add a new System Environment variable named `COQ_HOME` and set it to the path of your Coq installation. Then, within the `PATH` environment variable, add a new entry named `%COQ_HOME%\bin`. This will allow you to run any of the Coq executables from the command line (which is reqruied for the build script).*
    - After adding the `PATH` variable, you can verify that your setup is correct by opening a new terminal and running the command `coqc -v` in the command line. If you see the version of Coq that you are expecting, then your setup is correct.

## Setup & Build

1. **First-time setup** (clones and builds Picinae):
   ```
   .\first_time_setup.bat
   ```
   - The `windows_buiild.bat` script within Picinae assumes that you have installed Coq to the location `C:\Coq`. If you have installed Coq to a different location, you will need to modify the `windows_build.bat` script within the `Picinae` directory to point to your Coq installation location. 
   - If your Coq installation is in a different location, then you will need to run `first_time_setup.bat` twice: once to clone Picinae, and then again to build Picinae (after you have modified the `windows_build.bat` script).

2. **Build the atoi proof** (only non-Picinae files):
   ```
   .\windows_build.bat
   ```

3. **Clean compiled files** (preserves Picinae):
   ```
   .\clean.bat
   ```

## Project Structure
```
├── Picinae/                    Cloned master branch from https://github.com/CharlesAverill/Picinae
├── LiftedSource/               Lifted source file(s) provided by CS 6335 Staff
│   └── atoi_lo_atoi_armv8.v
├── Proofs/                     Correctness proof for atoi
│   ├── Lemmas/                 Supporting lemmas
│   └── Main_Proof.v            Main proof file
├── _CoqProject                 Coq project configuration        
├── clean.bat
├── first_time_setup.bat
└── windows_build.bat
```

## Notes
- All `.v` files in `LiftedSource/` and `Proofs/` are automatically discovered and compiled
- To add new lemmas, simply create `.v` files in `Proofs/Lemmas/` (no config updates needed)
- To clean Picinae separately, run `cd Picinae` then `.\clean.bat`
- If you are having an issue with the source files not properly recognizing the imports, reload your VSCode or IDE window. For VSCode, you can do this by pressing `Ctrl+Shift+P` and then typing `Reload Window`.

## Acknowledgements
The project was completed, in whole, by "the authors": Matthew Sheldon, Isabella Pereira, Jarrod Rogers, Naja-Lee Habboush, and Brandon Wang. This includes all proof source code as well as the build scripts. The project was completed as part of the "Language-Based Security" course at the University of Texas at Dallas, taught by Dr. Kevin Hamlen during the Fall 2025 semester.