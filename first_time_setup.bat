@echo off
REM First-time setup script for atoi proofs
REM (i) Clones Picinae into the local Picinae folder
REM (ii) Builds Picinae source files

echo ========================================
echo First Time Setup for atoi Proofs
echo ========================================
echo.

REM Check if Picinae folder exists and has content
if exist "Picinae\Picinae_core.v" (
    echo Picinae already exists. Skipping clone.
    echo If you want to re-clone, delete the Picinae folder first.
) else (
    echo Cloning Picinae from GitHub...
    if exist "Picinae" (
        rmdir /s /q "Picinae"
    )
    mkdir Picinae
    cd Picinae
    git init
    git remote add origin https://github.com/CharlesAverill/Picinae.git
    git fetch origin master
    git checkout master
    cd ..
    if errorlevel 1 (
        echo Error cloning Picinae repository
        pause
        exit /b 1
    )
    echo Picinae cloned successfully!
)

echo.
echo Building Picinae source files...
cd /d "%~dp0\Picinae"
call windows_build.bat
if errorlevel 1 (
    echo Error building Picinae source files
    cd /d "%~dp0"
    pause
    exit /b 1
)
cd /d "%~dp0"

echo.
echo ========================================
echo First-time setup completed successfully!
echo ========================================
echo You can now run windows_build.bat to build the atoi proofs.
pause
