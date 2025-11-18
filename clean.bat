@echo off
REM Clean script for atoi proofs
REM Removes all compiled files EXCEPT Picinae files

echo Cleaning atoi proofs (non-Picinae files)...

cd /d "%~dp0"

REM Remove compiled files from LiftedSource
if exist "LiftedSource" (
    del /q LiftedSource\*.vo 2>nul
    del /q LiftedSource\*.vok 2>nul
    del /q LiftedSource\*.vos 2>nul
    del /q LiftedSource\*.glob 2>nul
    del /q LiftedSource\*.aux 2>nul
)

REM Remove compiled files from Proofs
if exist "Proofs" (
    del /s /q Proofs\*.vo 2>nul
    del /s /q Proofs\*.vok 2>nul
    del /s /q Proofs\*.vos 2>nul
    del /s /q Proofs\*.glob 2>nul
    del /s /q Proofs\*.aux 2>nul
)

REM Remove Makefile.coq if it exists (in root only)
del /q Makefile.coq 2>nul
del /q Makefile.coq.conf 2>nul

echo Clean completed!
echo Note: Picinae files were NOT cleaned. To clean Picinae, run Picinae\clean.bat
pause
