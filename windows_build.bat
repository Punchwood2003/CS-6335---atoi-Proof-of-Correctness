@echo off
REM Build script for atoi proofs - uses root _CoqProject
REM Compiles all non-Picinae files: lifted source, helpers, and main proof

REM Check if Picinae has been compiled
if not exist "Picinae\Picinae_armv8_pcode.vo" (
    echo Error: Picinae has not been compiled yet.
    echo Please run first_time_setup.bat first.
    pause
    exit /b 1
)

echo Building atoi proofs...

REM Compile lifted source first with its namespace
echo Compiling LiftedSource/atoi_lo_atoi_armv8.v...
coqc -R Picinae Picinae -R LiftedSource atoiProof LiftedSource/atoi_lo_atoi_armv8.v
if errorlevel 1 (
    echo Error compiling lifted source
    exit /b 1
)

REM Compile helpers in dependency order
echo Compiling Helpers...

echo   Whitespace.v...
coqc -R Picinae Picinae -R Proofs/Helpers atoiProof.Helpers Proofs/Helpers/Whitespace.v
if errorlevel 1 (
    echo Error compiling Whitespace.v
    exit /b 1
)

echo   Digits.v...
coqc -R Picinae Picinae -R Proofs/Helpers atoiProof.Helpers Proofs/Helpers/Digits.v
if errorlevel 1 (
    echo Error compiling Digits.v
    exit /b 1
)

echo   Sign.v...
coqc -R Picinae Picinae -R Proofs/Helpers atoiProof.Helpers Proofs/Helpers/Sign.v
if errorlevel 1 (
    echo Error compiling Sign.v
    exit /b 1
)

echo   BitWidth.v...
coqc -R Picinae Picinae -R Proofs/Helpers atoiProof.Helpers Proofs/Helpers/BitWidth.v
if errorlevel 1 (
    echo Error compiling BitWidth.v
    exit /b 1
)

echo   Specification.v...
coqc -R Picinae Picinae -R Proofs/Helpers atoiProof.Helpers Proofs/Helpers/Specification.v
if errorlevel 1 (
    echo Error compiling Specification.v
    exit /b 1
)

echo   Invariants.v...
coqc -R Picinae Picinae -R Proofs/Helpers atoiProof.Helpers Proofs/Helpers/Invariants.v
if errorlevel 1 (
    echo Error compiling Invariants.v
    exit /b 1
)

echo   MainProofHelpers.v...
coqc -R Picinae Picinae -R Proofs/Helpers atoiProof.Helpers Proofs/Helpers/MainProofHelpers.v
if errorlevel 1 (
    echo Error compiling MainProofHelpers.v
    exit /b 1
)

echo   SpecificationProof.v...
coqc -R Picinae Picinae -R Proofs/Helpers atoiProof.Helpers Proofs/Helpers/SpecificationProof.v
if errorlevel 1 (
    echo Error compiling SpecificationProof.v
    exit /b 1
)

REM Compile main proof - include all paths with their namespaces
echo Compiling Proofs/Main_Proof.v...
coqc -R Picinae Picinae -R LiftedSource atoiProof -R Proofs/Helpers atoiProof.Helpers -R Proofs atoiProof Proofs/Main_Proof.v
if errorlevel 1 (
    echo Error compiling Main_Proof.v
    exit /b 1
)

echo.
echo Atoi proofs build succeeded!
pause
