@echo off
REM Build script for atoi proofs - uses root _CoqProject
REM Compiles all non-Picinae files: lifted source, lemmas, and main proof

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
coqc -R Picinae Picinae -R LiftedSource LiftedSource LiftedSource/atoi_lo_atoi_armv8.v
if errorlevel 1 (
    echo Error compiling lifted source
    exit /b 1
)

REM Compile lemmas with their namespaces
echo Compiling Proofs/Lemmas/basic_properties.v...
coqc -R Picinae Picinae -R Proofs Proofs Proofs/Lemmas/basic_properties.v
if errorlevel 1 (
    echo Error compiling basic_properties.v
    exit /b 1
)

REM Compile main proof - include all paths with their namespaces
echo Compiling Proofs/Main_Proof.v...
coqc -R Picinae Picinae -R LiftedSource LiftedSource -R Proofs Proofs Proofs/Main_Proof.v
if errorlevel 1 (
    echo Error compiling Main_Proof.v
    exit /b 1
)

echo.
echo Atoi proofs build succeeded!
pause
